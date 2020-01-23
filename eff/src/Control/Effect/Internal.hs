-- {-# OPTIONS_GHC -fno-max-relevant-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports -Wno-redundant-constraints -Wno-unused-foralls #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnboxedSums #-}

module Control.Effect.Internal where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.ST
import Control.Natural (type (~>))
import Data.Coerce
import Data.Kind (Constraint, Type)
import Data.Foldable
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (Any, Int(..), Int#, Proxy#, RealWorld, RuntimeRep(..), SmallMutableArray#, State#, TYPE, Void#, proxy#, runRW#, void#)
import GHC.TypeLits (ErrorMessage(..), Nat, TypeError)
import Unsafe.Coerce (unsafeCoerce)

import Control.Effect.Internal.Debug
import Control.Effect.Internal.Equality
import Control.Effect.Internal.PrimArray
import Control.Effect.Internal.SmallArray

-- -------------------------------------------------------------------------------------------------

type With :: TYPE rep -> Constraint
class With a where
  type WithC a :: Constraint
  with :: a -> (WithC a => r) -> r

instance With (a :~: b) where
  type WithC (a :~: b) = a ~ b
  with Refl x = x
  {-# INLINE with #-}

instance With (a ~# b) where
  type WithC (a ~# b) = a ~ b
  with Refl# x = x
  {-# INLINE with #-}

axiom :: a :~: b
axiom = unsafeCoerce Refl
{-# INLINE axiom #-}

-- type UnboxedRep :: Type -> RuntimeRep
-- type family UnboxedRep a
-- type Unboxed :: forall a -> TYPE (UnboxedRep a)
-- type family Unboxed a
--
-- type instance UnboxedRep Int = IntRep
-- type instance Unboxed Int = Int#

type DictRep :: Constraint -> Type
type family DictRep c
-- newtype Dict c = Dict { unDict :: DictRep c }

type WithDict :: Constraint -> Type -> Type
newtype WithDict c r = WithDict (c => r)
reflectDict :: forall c r. DictRep c -> (c => r) -> r
reflectDict d x = unsafeCoerce (WithDict @c @r x) $! d
{-# INLINE reflectDict #-}

-- -------------------------------------------------------------------------------------------------

type family xs ++ ys where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

-- -------------------------------------------------------------------------------------------------

type Effect = (Type -> Type) -> Type -> Type

data FramesK
  = ROOT Type -- ^ The type of the computation’s state token. Accessible via 'S'.
         Type -- ^ The type of the computation’s final result. Accessible via 'R'.
  | CELL Type FramesK
  | PROMPT Effect [Effect] Type [[Effect]] FramesK

type FrameK = FramesK -> FramesK

type S :: FramesK -> Type
type family S fs where
  S ('ROOT s _) = s
  S (_ fs) = S fs

type R :: FramesK -> Type
type family R fs where
  R ('ROOT _ r) = r
  R (_ fs) = R fs

-- | The representation of the frame @f@ above a stack of underlying frames @fs@.
type Frame :: FrameK -> FramesK -> Type
type family Frame f fs where
  Frame ('CELL s) _ = s
  Frame ('PROMPT eff effs i effss) fs = Prompt eff effs i effss fs

type FrameEffect :: FrameK -> Effect
type family FrameEffect f where
  FrameEffect ('CELL s) = Cell s
  FrameEffect ('PROMPT eff _ _ _) = eff

-- | A proof that the /top frames/ of two 'FramesK' types are equal. If there are no frames, which
-- is to say they are 'ROOT', they must be completely identical.
type (^~) :: FramesK -> FramesK -> TYPE ('TupleRep '[])
newtype fs1 ^~ fs2 = UnsafeTopsEq Void#
{-# COMPLETE TopsFrame #-}

pattern TopsRefl :: forall fs1 fs2. () => fs1 ~ fs2 => fs1 ^~ fs2
pattern TopsRefl <- ((\_ -> axiom @fs1 @fs2) -> Refl) where TopsRefl = UnsafeTopsEq void#

pattern TopsFrame
  :: forall fs1 fs2. () => forall (f :: FrameK) fs3 fs4. (fs1 ~ f fs3, fs2 ~ f fs4) => fs1 ^~ fs2
pattern TopsFrame = TopsFrame# Refl# Refl#

pattern TopsFrame#
  :: forall fs1 fs2. () => forall (f :: FrameK) fs3 fs4. fs1 ~# f fs3 -> fs2 ~# f fs4 -> fs1 ^~ fs2
pattern TopsFrame# a b <- ((\_ -> (# unsafeRefl# void#, unsafeRefl# void# #)) -> (# a, b #))
  where TopsFrame# Refl# Refl# = UnsafeTopsEq void#

topsTrans :: fs1 ^~ fs2 -> fs2 ^~ fs3 -> fs1 ^~ fs3
topsTrans TopsRefl tops = tops
topsTrans TopsFrame TopsRefl = TopsFrame
topsTrans TopsFrame TopsFrame = TopsFrame
{-# INLINE topsTrans #-}

-- | The primitive state pseudo-effect, which provides access to a single cell of mutable state of
-- type @s@. Unlike real effects, 'Cell' only has one handler, 'runCell'. Users should not use
-- 'Cell' directly, but should instead use the ordinary 'State' effect; the default handler for
-- 'State' is internally implemented as a small wrapper around 'Cell'.
type Cell :: Type -> Effect
data Cell s :: Effect

type family Handles eff :: Constraint where
  Handles (Cell s) = NoHandling Cell (Cell s)
  Handles _ = ()
type family NoHandling c eff where
  NoHandling c eff = TypeError
    ( 'Text "no instance for ‘" ':<>: 'ShowType eff ':<>: 'Text "’;"
    ':$$: 'Text "  " ':<>: 'ShowType c ':<>: 'Text " is a primitive effect and cannot be handled" )

-- | Primitive effects are uninhabited, so we can obtain a proof of 'Handles' by forcing an effect
-- value.
handles :: eff m a -> Handles eff :~: (() :: Constraint)
handles !_ = axiom
{-# INLINE handles #-}

withHandlesImpliesPrompt
  :: forall f eff m a r. (Handles eff, eff ~ FrameEffect f)
  => (forall effs i effss. f ~ 'PROMPT eff effs i effss => Proxy# ('PROMPT eff effs i effss) -> r)
  -> r
withHandlesImpliesPrompt k =
  ( with (axiom @f @('PROMPT eff effs i effss))
  $ k @effs @i @effss proxy#
  ) :: forall (effs :: [Effect]) (i :: Type) (effss :: [[Effect]]). r

-- -------------------------------------------------------------------------------------------------

type (:<) :: Effect -> [Effect] -> Constraint
class eff :< effs where
  reifyIndex :: Int
instance {-# OVERLAPPING #-} eff :< (eff ': effs) where
  reifyIndex = 0
  {-# INLINE reifyIndex #-}
instance eff :< effs => eff :< (eff' ': effs) where
  reifyIndex = reifyIndex @eff @effs + 1
  {-# INLINE reifyIndex #-}

type (:<<) :: [Effect] -> [Effect] -> Constraint
class effs1 :<< effs2 where
  reifySubIndex :: Int
instance {-# OVERLAPPING #-} effs :<< effs where
  reifySubIndex = 0
  {-# INLINE reifySubIndex #-}
instance effs1 :<< effs2 => effs1 :<< (eff ': effs2) where
  reifySubIndex = reifySubIndex @effs1 @effs2 + 1
  {-# INLINE reifySubIndex #-}

type Depth :: FramesK -> Constraint
class Depth fs where
  reifyDepth :: Int
instance Depth ('ROOT s r) where
  reifyDepth = 0
  {-# INLINE reifyDepth #-}
instance Depth fs => Depth (f fs) where
  reifyDepth = reifyDepth @fs + 1
  {-# INLINE reifyDepth #-}

type (:<#) :: FrameK -> FramesK -> Constraint
class f :<# fs where
  reifyIndexF :: Int
instance {-# OVERLAPPING #-} Depth (f fs) => f :<# f fs where
  reifyIndexF = reifyDepth @(f fs) - 1
  {-# INLINE reifyIndexF #-}
instance f :<# fs => f :<# f' fs where
  reifyIndexF = reifyIndexF @f @fs
  {-# INLINE reifyIndexF #-}

type (:<<#) :: FramesK -> FramesK -> Constraint
class fs1 :<<# fs2 where
  reifySubIndexF :: Int
instance {-# OVERLAPPING #-} Depth fs => fs :<<# fs where
  reifySubIndexF = reifyDepth @fs - 1
  {-# INLINE reifySubIndexF #-}
instance (fs2 ~ f fs3, fs1 :<<# fs3) => fs1 :<<# fs2 where
  reifySubIndexF = reifySubIndexF @fs1 @fs3
  {-# INLINE reifySubIndexF #-}

type instance DictRep (eff :< effs) = Int
type instance DictRep (effs1 :<< effs2) = Int
type instance DictRep (Depth fs) = Int
type instance DictRep (f :<# fs) = Int
type instance DictRep (fs1 :<<# fs2) = Int

-- -------------------------------------------------------------------------------------------------

newtype Eff effs a = Eff
  { unEff :: forall effss fs1
           . (forall fs2. fs1 ^~ fs2 -> a -> Context effs effss fs2 -> ST (S fs2) (R fs2))
          -> Context effs effss fs1 -> ST (S fs1) (R fs1)
  }

-- | Note: we store @effs ':->>' fs@ separately from @effss ':=>>' fs@ (rather than simply storing
-- a single value of type @(effs ': effss) ':=>>' fs@) to avoid a pointer indirection when
-- retrieving the topmost targets. It isn’t clear if this is beneficial in general, as it requires
-- an additional argument to be passed on the stack; benchmarking the difference would be useful.
newtype Context effs effss fs = Context# (# effs :->> fs, effss :=>> fs, Frames# fs #)
pattern Context :: effs :->> fs -> effss :=>> fs -> Frames fs -> Context effs effss fs
pattern Context a b c <- Context# (# a, b, (BoxFrames -> c) #)
  where Context a b (BoxFrames c) = Context# (# a, b, c #)
{-# COMPLETE Context #-}

-- | A stack of metacontinuation frames. The 'Int#' field contains the logical size of the current
-- frames stack; the 'SmallMutableArray#' is usually a little larger than the logical size so we
-- don’t have to do so much copying. When the stack overflows, we allocate a new, larger stack and
-- copy the old frames into the new stack (and the old stack can be deallocated by the GC).
newtype Frames# fs = Frames# (# Int#, SmallMutableArray# (S fs) Any #)

-- | A boxed version of 'Frames#'. This is more convenient to work with, so we use it in places
-- where GHC can optimize away the boxing anyway.
data Frames fs = BoxFrames (Frames# fs)
pattern Frames :: Int -> SmallMutableArray (S fs) Any -> Frames fs
pattern Frames a b <- BoxFrames (Frames# (# (I# -> a), (SmallMutableArray -> b) #))
  where Frames (I# a) (SmallMutableArray b) = BoxFrames (Frames# (# a, b #))
{-# COMPLETE Frames #-}

type Prompt :: Effect -> [Effect] -> Type -> [[Effect]] -> FramesK -> Type
data Prompt eff effs i effss fs = Prompt
  { pCont :: i -> Context effs effss fs -> ST (S fs) (R fs)
  -- ^ The continuation between this prompt and the parent prompt.
  , pTargets :: (eff ': effs) :->> 'PROMPT eff effs i effss fs
  , pTargetss :: (effs ': effss) :=>> fs
  , pHandler :: forall effs'. Handling# eff effs i effs' -> eff (Eff effs') ~> Eff effs'
  }

-- -------------------------------------------------------------------------------------------------

{- The arrow zoo:

  * eff   :->  fs — target indirection index
  * effs  :->> fs — target indirection vector
  * effss :=>> fs — target indirection vector stack
  * effs  :~>> fs — target remapping stack

-}

type (:->) :: Effect -> FramesK -> Type
newtype eff :-> fs = Target { unTarget :: Int }

-- type (:=>) :: [Effect] -> FramesK -> Type
-- newtype effs :=> fs = TargetsSegment { unTargetsSegment :: PrimArray Int }
--
-- -- | The maximum size of a 'TargetsSegment'.
-- maxSegmentSize :: Int
-- maxSegmentSize = 32
-- {-# INLINE maxSegmentSize #-}

-- type (:->>) :: [Effect] -> FramesK -> Type
-- data effs :->> fs where
--   NoTargets :: '[] :->> fs
--   Targets
--     :: (effs1 ++ effs2) ~# effs
--     -> {-# UNPACK #-} effs1 :=> fs
--     -> effs2 :->> fs
--     -> effs :->> fs

type (:->>) :: [Effect] -> FramesK -> Type
newtype effs :->> fs = Targets { unTargets :: PrimArray Int }
-- TODO: Redefine PrimArray using UnliftedNewtypes to skip an extra layer of indirection.
-- TODO: Represent (:->>) in chunks if it gets too long.

type (:=>>) :: [[Effect]] -> FramesK -> Type
data effss :=>> fs where
  NoTargetss :: '[] :=>> fs
  PushTargets ::
    { peekTargets :: effs :->> fs
    , popTargets :: effss :=>> fs
    } -> (effs ': effss) :=>> fs

type (:~>>) :: [Effect] -> FramesK -> Type
data effs :~>> fs where
--   Id ::
--   Lift :: {-# UNPACK #-} effs1 :⊆: effs2 ->

-- -------------------------------------------------------------------------------------------------
-- frames

-- | A restricted form of 'unsafeCoerce' that only works for converting to/from 'Any'. Still just as
-- unsafe, but makes it slightly more difficult to accidentally misuse.
pattern Any :: forall a. a -> Any
pattern Any a <- (unsafeCoerce -> a)
  where Any = unsafeCoerce

-- | Used to explicitly overwrite references to values that should not be retained by the GC.
null# :: Any
null# = Any ()

newEmptyFrames :: ST s (Frames ('ROOT s r))
newEmptyFrames = Frames 0 <$> newSmallArray 32 null#

withDepthOf :: forall fs r. Frames fs -> (Depth fs => r) -> r
withDepthOf (Frames len _) = reflectDict @(Depth fs) len

lookupFrame
  :: forall f fs2 r. (DebugCallStack, f :<# fs2)
  => Frames fs2
  -> (forall fs1. f fs1 :<<# fs2 => Proxy# fs1 -> Frame f fs1 -> ST (S fs2) r)
  -> ST (S fs2) r
lookupFrame (Frames len fs) k = do
  { let idx = reifyIndexF @f @fs2
  ; assertM $ idx < len
  ; Any f <- readSmallArray fs idx
  ; reflectDict @(f fs1 :<<# fs2) idx
  $ k @fs1 proxy# f
  } :: forall (fs1 :: FramesK). ST (S fs2) r

-- | Looks up a 'Frame' given a 'Target' into a stack of 'Frames'. The result is returned by passing
-- it to the given continuation so that the @f@ and @fs2@ variables can be bound existentially.
indexFrame
  :: forall eff fs1 r. DebugCallStack => eff :-> fs1 -> Frames fs1
  -> (forall f fs2. (eff ~ FrameEffect f, f fs2 :<<# fs1)
      => Proxy# (f fs2) -> Frame f fs2 -> ST (S fs1) r)
  -> ST (S fs1) r
indexFrame (Target idx) (Frames len fs) k = do
  { assertM $ idx < len
  ; with (axiom @eff @(FrameEffect f)) do
  { Any f <- readSmallArray fs idx
  ; reflectDict @(f fs2 :<<# fs1) idx
  $ k @f @fs2 proxy# f
  }} :: forall (f :: FrameK) (fs2 :: FramesK). ST (S fs1) r

pushFrame :: Frame f fs -> Frames fs -> ST (S fs) (Frames (f fs))
pushFrame f (Frames len fs1) = do
  fs2 <- if
    | len == sizeofSmallMutableArray fs1 -> do
        -- out of space, resize and copy
        fs2 <- newSmallArray (len * 2) null#
        copySmallMutableArray fs2 0 fs1 0 len
        pure fs2
    | otherwise -> do
        -- no need to resize, reuse the input array
        assertM $ len >= 0
        assertM $ len < sizeofSmallMutableArray fs1
        pure fs1
  assertM $ len + 1 <= sizeofSmallMutableArray fs2
  writeSmallArray fs2 len (Any f)
  pure $ Frames (len + 1) fs2

popFrame :: Frames (f fs) -> ST (S fs) (Frame f fs, Frames fs)
popFrame (Frames len fs) = do
  Any f <- readSmallArray fs (len - 1)
  writeSmallArray fs len null#
  pure (f, Frames (len - 1) fs)

-- -------------------------------------------------------------------------------------------------
-- targets

newTarget :: forall f fs. f :<# fs => FrameEffect f :-> fs
newTarget = Target $ reifyIndexF @f @fs

noTargets :: '[] :->> fs
noTargets = Targets mempty

weakenTargets :: fs1 :<<# fs2 => effs :->> fs1 -> effs :->> fs2
weakenTargets (Targets ts) = Targets ts

lookupTarget :: forall eff effs fs. (DebugCallStack, eff :< effs) => effs :->> fs -> eff :-> fs
lookupTarget (Targets ts) = Target $ indexPrimArray ts (reifyIndex @eff @effs)

pushTarget :: eff :-> fs -> effs :->> fs -> (eff ': effs) :->> fs
pushTarget (Target t) (Targets ts1) = Targets $ runPrimArray do
  let len = sizeofPrimArray ts1
  ts2 <- newPrimArray (len + 1)
  writePrimArray ts2 0 t
  copyPrimArray ts2 1 ts1 0 len
  pure ts2

dropTargets
  :: forall effs1 effs2 fs. (DebugCallStack, effs1 :<< effs2)
  => effs2 :->> fs -> effs1 :->> fs
dropTargets (Targets ts) =
  let idx = reifySubIndex @effs1 @effs2
      len = sizeofPrimArray ts - idx
  in Targets $ clonePrimArray ts idx len

-- -------------------------------------------------------------------------------------------------
-- core Eff operations

instance Functor (Eff effs) where
  fmap f (Eff m) = Eff \k -> m \tops a -> k tops (f a)
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff \k -> k TopsRefl a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff m >>= f = Eff \k -> m \tops1 a -> unEff (f a) \tops2 -> k (topsTrans tops1 tops2)
  {-# INLINE (>>=) #-}

run :: Eff '[] a -> a
run (Eff m) = runST do
  fs <- newEmptyFrames
  m (\TopsRefl v _ -> pure v) (Context noTargets NoTargetss fs)

lift :: effs1 :<< effs2 => Eff effs1 ~> Eff effs2
lift (Eff m) = Eff \k (Context ts1 tss1 fs1) ->
  let ctx = Context (dropTargets ts1) (PushTargets ts1 tss1) fs1
  in m (\tops a (Context _ (PushTargets ts2 tss2) fs2) -> k tops a (Context ts2 tss2 fs2)) ctx

-- -------------------------------------------------------------------------------------------------
-- Handling

type Handling :: Effect -> [Effect] -> Type -> [Effect] -> Constraint
class Handling eff effs i effs' | eff effs' -> i effs where
  reifyHandlerIndex :: Int
type instance DictRep (Handling eff effs i effs') = Int

reflectHandling
  :: forall eff effs1 effss i fs1 effs2 fs2 r. 'PROMPT eff effs1 i effss fs1 :<<# fs2
  => effs2 :->> fs2
  -- ^ A proof that this list of effects is fully handled by the current stack of frames.
  -> (Handling eff effs1 i effs2 => r) -> r
reflectHandling !_ =
  reflectDict @(Handling eff effs1 i effs2) $ reifySubIndexF @('PROMPT eff effs1 i effss fs1) @fs2

withHandling
  :: forall eff effs' fs effs i r. Handling eff effs i effs'
  => effs' :->> fs
  -- ^ A proof that we’re in a context where the 'Handling' constraint actually applies.
  -> (forall effss. 'PROMPT eff effs i effss :<# fs => Proxy# effss -> r)
  -> r
withHandling !_ k =
  ( reflectDict @('PROMPT eff effs i effss :<# fs) (reifyHandlerIndex @eff @effs @i @effs')
  $ k @effss proxy#
  ) :: forall (effss :: [[Effect]]). r

type Handling# :: Effect -> [Effect] -> Type -> [Effect] -> TYPE 'IntRep
newtype Handling# eff effs i effs' = Handling# { handlerIndex# :: Int# }

reifyHandling# :: forall eff effs i effs'. Handling eff effs i effs' => Handling# eff effs i effs'
reifyHandling# = let !(I# n) = reifyHandlerIndex @eff @effs @i @effs' in Handling# n

reflectHandling#
  :: forall eff effs i effs' r. Handling# eff effs i effs' -> (Handling eff effs i effs' => r) -> r
reflectHandling# (Handling# n) = reflectDict @(Handling eff effs i effs') (I# n)

-- -------------------------------------------------------------------------------------------------
-- Eff operations that use Handling

liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff m) = Eff \k (Context ts1 tss1 fs1) ->
  withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
  lookupFrame @('PROMPT eff effs i effss) fs1 \_ p ->
    let ctx = Context (weakenTargets $ pTargets p) (PushTargets ts1 tss1) fs1
    in m (\tops a (Context _ (PushTargets ts2 tss2) fs2) -> k tops a (Context ts2 tss2 fs2)) ctx

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \k ctx@(Context ts _ fs) ->
  with (handles e) $
  indexFrame (lookupTarget @eff ts) fs \(_ :: Proxy# (f fs)) p ->
  withHandlesImpliesPrompt @f \(_ :: Proxy# ('PROMPT eff effs2 i effss)) ->
  reflectHandling @eff @effs2 @effss @i @fs ts $
    unEff (pHandler p reifyHandling# e) k ctx

handle
  :: forall eff a effs. Handles eff
  => (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f (Eff m) = Eff \k1 (Context ts1 tss1 fs1 :: Context effs effss1 fs1) ->
  withDepthOf fs1 do
    let k2 :: forall fs2. 'PROMPT eff effs a effss1 fs1 ^~ fs2
           -> a -> Context (eff ': effs) '[] fs2 -> ST (S fs2) (R fs2)
        k2 TopsFrame a (Context _ _ ffs3) = do
          (f3, fs3) <- popFrame ffs3
          let !(PushTargets ts3 tss3) = pTargetss f3
          pCont f3 a (Context ts3 tss3 fs3)

        f1 :: Prompt eff effs a effss1 fs1
        f1 = Prompt
          { pCont = k1 TopsRefl
          , pTargets = ts2
          , pTargetss = PushTargets ts1 tss1
          , pHandler = \n e -> reflectHandling# n $ f e
          }

        ts2 :: (eff ': effs) :->> 'PROMPT eff effs a effss1 fs1
        ts2 = pushTarget (newTarget @('PROMPT eff effs a effss1)) (weakenTargets ts1)

    fs2 <- pushFrame f1 fs1
    m k2 (Context ts2 NoTargetss fs2)

-- -------------------------------------------------------------------------------------------------

-- type (:⊆:) :: k -> k -> Type
-- newtype a :⊆: b = SubIndex { unSubIndex :: Int }

{-

type Holds = (~) (() :: Constraint)
type Proof = (:~:) (() :: Constraint)

axiomC :: forall a. Proof a
axiomC = axiom
{-# INLINE axiomC #-}

type Effect = (Type -> Type) -> Type -> Type

data Cell (s :: Type) :: Effect

type family Handles eff :: Constraint where
  Handles (Cell s) = NoHandling Cell (Cell s)
  Handles _ = ()
type family NoHandling c eff where
  NoHandling c eff = TypeError
    ( 'Text "no instance for ‘" ':<>: 'ShowType eff ':<>: 'Text "’;"
    ':$$: 'Text "  " ':<>: 'ShowType c ':<>: 'Text " is a primitive effect and cannot be handled" )

-- | Primitive effects are uninhabited, so we can obtain a proof of 'Handles' by forcing an effect
-- value.
handles :: eff m a -> Proof (Handles eff)
handles !_ = axiomC
{-# INLINE handles #-}

data (fs :: FramesK) :^~: (fs' :: FramesK) where
  TopsRefl :: fs :^~: fs
  TopsFrame :: forall (f :: FrameK) fs fs'. f fs :^~: f fs'

class fs ^~ fs' where
  topsEq :: fs :^~: fs'
instance {-# INCOHERENT #-} fs ^~ fs where
  topsEq = TopsRefl
  {-# INLINE topsEq #-}
instance f fs'' ~ fs' => (f :: FrameK) fs ^~ fs' where
  topsEq = TopsFrame
  {-# INLINE topsEq #-}

instance With (fs :^~: fs') where
  type WithC (fs :^~: fs') = fs ^~ fs'
  with TopsRefl x = x
  with TopsFrame x = x
  {-# INLINE with #-}

topsRoot :: forall r fs. 'ROOT r ^~ fs => 'ROOT r :~: fs
topsRoot = case topsEq @('ROOT r) @fs of TopsRefl -> Refl
{-# INLINE topsRoot #-}

withTopFramesEq :: forall f fs fs' r. f fs ^~ fs' => (forall fs''. fs' ~ f fs'' => r) -> r
withTopFramesEq x = case topsEq @(f fs) @fs' of
  TopsRefl -> x
  TopsFrame -> x
{-# INLINE withTopFramesEq #-}

topsTrans :: forall fs1 fs2 fs3. (fs1 ^~ fs2, fs2 ^~ fs3) => fs1 :^~: fs3
topsTrans = case topsEq @fs1 @fs2 of
  TopsRefl -> case topsEq @fs2 @fs3 of
    TopsRefl -> TopsRefl
    TopsFrame -> TopsFrame
  TopsFrame -> case topsEq @fs2 @fs3 of
    TopsRefl -> TopsFrame
    TopsFrame -> TopsFrame


type family FrameEffect f where
  FrameEffect ('CELL s) = Cell s
  FrameEffect ('PROMPT eff _ _ _) = eff

withHandlesImpliesPrompt
  :: forall eff f r. (Handles eff, eff ~ FrameEffect f)
  => (forall effs i effss. f ~ 'PROMPT eff effs i effss => Proxy# ('PROMPT eff effs i effss) -> r)
  -> r
withHandlesImpliesPrompt x =
  with (axiom @f @('PROMPT eff effs i effss)) $ x @effs @i @effss proxy#
  :: forall (effs :: [Effect]) (i :: Type) (effss :: [[Effect]]). r
{-# INLINE withHandlesImpliesPrompt #-}

decomposeCell :: forall s f. Cell s ~ FrameEffect f => f :~: 'CELL s
decomposeCell = axiom
{-# INLINE decomposeCell #-}

-- | If one 'FramesK' is contained within the other, their roots must be equal.
rootsEq :: forall fs fs'. fs :<<# fs' => R fs :~: R fs'
rootsEq = subIndexValF @fs @fs' `seq` axiom
{-# INLINE rootsEq #-}

class (eff :: Effect) :< (effs :: [Effect]) where
  indexVal :: Int
instance {-# OVERLAPPING #-} eff :< (eff ': effs) where
  indexVal = 0
  {-# INLINE indexVal #-}
instance eff :< effs => eff :< (eff' ': effs) where
  indexVal = indexVal @eff @effs + 1
  {-# INLINE indexVal #-}

class Length (fs :: FramesK) where
  lengthVal :: Int
instance Length ('ROOT r) where
  lengthVal = 0
  {-# INLINE lengthVal #-}
instance Length fs => Length ('CELL s fs) where
  lengthVal = lengthVal @fs + 1
  {-# INLINE lengthVal #-}
instance Length fs => Length ('PROMPT eff effs i effss fs) where
  lengthVal = lengthVal @fs + 1
  {-# INLINE lengthVal #-}

class (f :: FrameK) :<# (fs :: FramesK) where
  indexValF :: Int
instance {-# OVERLAPPING #-} Length (f fs) => f :<# f fs where
  indexValF = lengthVal @(f fs) - 1
  {-# INLINE indexValF #-}
instance f :<# fs => f :<# f' fs where
  indexValF = indexValF @f @fs
  {-# INLINE indexValF #-}

class (effs :: [Effect]) :<< (effs' :: [Effect]) where
  subIndexVal :: Int
instance {-# OVERLAPPING #-} effs :<< effs where
  subIndexVal = 0
  {-# INLINE subIndexVal #-}
instance (effs' ~ (eff ': effs''), effs :<< effs'') => effs :<< effs' where
  subIndexVal = subIndexVal @effs @effs'' + 1
  {-# INLINE subIndexVal #-}

class (fs :: FramesK) :<<# (fs' :: FramesK) where
  subIndexValF :: Int
instance {-# OVERLAPPING #-} Length fs => fs :<<# fs where
  subIndexValF = lengthVal @fs - 1
  {-# INLINE subIndexValF #-}
instance (ffs' ~ f fs', fs :<<# fs') => fs :<<# ffs' where
  subIndexValF = subIndexValF @fs @fs'
  {-# INLINE subIndexValF #-}

newtype WithLength fs r = WithLength (Length fs => r)
withLength :: forall fs r. Int -> (Length fs => r) -> r
withLength n x = unsafeCoerce (WithLength @fs x) $! n
{-# INLINE withLength #-}

withLengthOf :: forall fs r. Frames fs -> (Length fs => r) -> r
withLengthOf (Frames fs) = withLength @fs (sizeofSmallArray fs)
{-# INLINE withLengthOf #-}

newtype WithIndexF f fs r = WithIndexF (f :<# fs => r)
withIndexF :: forall f fs r. Int -> (f :<# fs => r) -> r
withIndexF n x = unsafeCoerce (WithIndexF @f @fs x) $! n
{-# INLINE withIndexF #-}

newtype WithSubIndexF fs fs' r = WithSubIndexF (fs :<<# fs' => r)
withSubIndexF :: forall fs fs' r. Int -> (fs :<<# fs' => r) -> r
withSubIndexF n x = unsafeCoerce (WithSubIndexF @fs @fs' x) $! n
{-# INLINE withSubIndexF #-}

withWeakenSubIndex :: forall f fs fs' r. f fs :<<# fs' => (fs :<<# fs' => r) -> r
withWeakenSubIndex = withSubIndexF @fs @fs' (subIndexValF @(f fs) @fs' - 1)
{-# INLINE withWeakenSubIndex #-}

-- | Like ':<<', but only at the type level; it carries no actual evidence. This is slightly more
-- efficient, since it doesn’t have to be passed around, but of course it means the index value
-- cannot actually be accessed.
type family fs :<<! fs' :: Constraint where
  fs :<<! fs = ()
  fs :<<! _ fs' = fs :<<! fs'

eraseSub :: forall fs fs'. fs :<<# fs' => Proof (fs :<<! fs')
eraseSub = subIndexValF @fs @fs' `seq` axiom
{-# INLINE eraseSub #-}

attachSub :: forall fs fs' r. (Length fs, fs :<<! fs') => (fs :<<# fs' => r) -> r
attachSub = withSubIndexF @fs @fs' (subIndexValF @fs @fs)
{-# INLINE attachSub #-}

weakenSub :: forall fs f fs'. fs :<<! fs' => Proof (fs :<<! f fs')
weakenSub = axiom
{-# INLINE weakenSub #-}

transSub :: forall fs1 fs2 fs3. (fs1 :<<! fs2, fs2 :<<! fs3) => Proof (fs1 :<<! fs3)
transSub = axiom
{-# INLINE transSub #-}

transAttachSub :: forall fs1 fs2 fs3 r. (fs1 :<<# fs2, fs2 :<<! fs3) => (fs1 :<<# fs3 => r) -> r
transAttachSub = withSubIndexF @fs1 @fs3 (subIndexValF @fs1 @fs2)
{-# INLINE transAttachSub #-}

type family effs :->>! fs :: Constraint where {}
eraseTargets :: forall effs fs. effs :->> fs -> Proof (effs :->>! fs)
eraseTargets !_ = axiom
{-# INLINE eraseTargets #-}

newtype Eff effs a = Eff
  { unEff :: forall effss fs
           . (forall fs'. fs ^~ fs' => a -> Context effs effss fs' -> R fs')
          -> Context effs effss fs -> R fs }

-- mkEff :: forall effs a. (forall fs. Proxy# fs -> (a -> Frames fs -> R fs) -> effs :->> fs -> Frames fs -> R fs) -> Eff effs a
-- mkEff f = Eff (f (proxy# @_ @fs) :: forall fs. (a -> Frames fs -> R fs) -> effs :->> fs -> Frames fs -> R fs)
-- {-# INLINE mkEff #-}

data Context effs effss fs = Context
  { targetss :: (effs ': effss) :->>> fs
  , frames :: {-# UNPACK #-} Frames fs }

-- | An array of metacontinuation 'Frame's. Newer frames are added to the /end/ of the array, so the
-- array is stored “backwards” relative to the order the frames appear in 'FramesK'. This ensures
-- indexes into 'Frames' are stable—an index will refer to the same frame even if new frames are
-- added later.
newtype Frames (fs :: FramesK) = Frames { unFrames :: SmallArray Any }

type family Frame f fs where
  Frame ('CELL s) _ = s
  Frame ('PROMPT eff effs i effss) fs = Handler eff effs i effss fs

-- | A slice of a stack of 'Frames'. @fs@ must be a subset of @fs'@, and the captured frames include
-- all the frames in @fs'@ that are /not/ in @fs@. The first frame included in the capture is @f@,
-- which in practice is always a 'PROMPT' and is used to ensure the captured frames are restored
-- onto a stack of the appropriate shape.
data CapturedFrames (f :: FrameK) (fs :: FramesK) (fs' :: FramesK)
  = f fs :<<# fs' => CapturedFrames { unCapturedFrames :: {-# UNPACK #-} SmallArray Any }

firstCapturedFrame :: CapturedFrames f fs fs' -> Frame f fs
firstCapturedFrame (CapturedFrames fs) = unsafeCoerce $ indexSmallArray fs 0
{-# INLINE firstCapturedFrame #-}

data Handler eff effs i effss fs = Handler
  { hTargets :: {-# UNPACK #-} (eff ': effs) :->> 'PROMPT eff effs i effss fs
  , hTargetss :: (effs ': effss) :->>> fs
  , hSend :: forall effs'. Handling eff effs i effs' => eff (Eff effs') ~> Eff effs'
  , hCont :: forall fs'. fs ^~ fs' => i -> Context effs effss fs' -> R fs' }

-- | The /target indirection vector/, which maps each effect in the row of effects to a particular
-- handler. This layer of indirection incurs a small performance cost, but it allows far greater
-- flexibility in how the row of effects may be manipulated.
--
-- Without the indirection, the row of effects would need to be exactly the same length as the stack
-- of metacontinuation frames, and each effect would be handled by its corresponding frame. This
-- makes it impossible for a handler to locally introduce a new effect and handle it immediately
-- without the effect leaking out into the handler’s type. The indirection vector allows effects to
-- be added underneath existing effects, reordered, and deduplicated.
--
-- __Unlike__ 'Frames', ':->>' is ordered from newest to oldest, so the target for the first element
-- of @effs@ is always stored at index @0@. This is convenient because it allows indexes into the
-- array to be more easily calculated at compile-time from the type information, and it isn’t
-- important that the indexes be dynamically stable in the same way it is for 'Frames'.
newtype (effs :: [Effect]) :->> (fs :: FramesK) = Targets { unTargets :: PrimArray Int }
newtype (eff :: Effect) :-> (fs :: FramesK) = Target { unTarget :: Int }



-- data (effs :: [Effect]) :->> (fs :: FramesK) where
--   Targets
--     :: {-# UNPACK #-} PrimArray Int
--     -- ^ A vector of targets
--     -> effs' :->> fs
--     -> effs :->> fs

newtype (effs :: [Effect]) :=>> (effs' :: [Effect]) = Mapping { unMapping :: PrimArray Int }

data effss :->>> fs where
  RootTargets :: {-# UNPACK #-} effs :->> fs -> '[effs] :->>> fs
  RemapTargets
    :: {-# UNPACK #-} effs :->> fs
    -> {-# UNPACK #-} effs :=>> effs'
    -> (effs' ': effss) :->>> fs
    -> (effs ': effs' ': effss) :->>> fs

peekTargets :: (effs ': effss) :->>> fs -> effs :->> fs
peekTargets = \case
  RootTargets ts -> ts
  PushTargets ts _ -> ts
{-# INLINE peekTargets #-}

popTargets :: (effs ': effs' ': effss) :->>> fs -> (effs' ': effss) :->>> fs
popTargets (PushTargets _ tss) = tss
{-# INLINE popTargets #-}

weakenTargetss :: fs :<<# fs' => effss :->>> fs -> effss :->>> fs'
weakenTargetss = coerce
{-# INLINE weakenTargetss #-}

-- unsafeStrengthenTargetss :: effs :->>> f fs -> effs :->>> fs
-- unsafeStrengthenTargetss = coerce
-- {-# INLINE unsafeStrengthenTargetss #-}

rootFrames :: Frames ('ROOT r)
rootFrames = Frames mempty
{-# INLINE rootFrames #-}

noTargets :: '[] :->> fs
noTargets = Targets mempty
{-# INLINE noTargets #-}

weakenTargets :: forall fs fs' effs. fs :<<# fs' => effs :->> fs -> effs :->> fs'
weakenTargets ts = subIndexValF @fs @fs' `seq` coerce ts
{-# INLINE weakenTargets #-}

-- unsafeStrengthenTargets :: effs :->> f fs -> effs :->> fs
-- unsafeStrengthenTargets = coerce
-- {-# INLINE unsafeStrengthenTargets #-}

pushFrame :: forall f fs. Frame f fs -> Frames fs -> Frames (f fs)
pushFrame h (Frames hs) = Frames $ runSmallArray do
  let len = sizeofSmallArray hs
  hs' <- newSmallArray (len + 1) (error "pushFrame: value left uninitialized")
  copySmallArray hs' 0 hs 0 len
  writeSmallArray hs' len (unsafeCoerce h)
  pure hs'

newTarget :: forall f fs. f :<# fs => FrameEffect f :-> fs
newTarget = Target $ indexValF @f @fs
{-# INLINE newTarget #-}

lookupTarget :: forall eff effs fs. eff :< effs => effs :->> fs -> eff :-> fs
lookupTarget (Targets ts) = Target $ indexPrimArray ts (indexVal @eff @effs)

pushTarget :: forall eff effs fs. eff :-> fs -> effs :->> fs -> (eff ': effs) :->> fs
pushTarget (Target t) (Targets ts) = Targets $ runPrimArray do
  let len = sizeofPrimArray ts
  ts' <- newPrimArray (len + 1)
  writePrimArray ts' 0 t
  copyPrimArray ts' 1 ts 0 len
  pure ts'

popTarget :: forall eff effs fs. (eff ': effs) :->> fs -> effs :->> fs
popTarget (Targets ts) = Targets $ clonePrimArray ts 1 (sizeofPrimArray ts)

dropTargets :: forall effs effs' fs. effs :<< effs' => effs' :->> fs -> effs :->> fs
dropTargets (Targets ts) = Targets $ clonePrimArray ts (subIndexVal @effs @effs') (sizeofPrimArray ts)

peekFrame :: Frames (f fs) -> Frame f fs
peekFrame (Frames fs) = unsafeCoerce $ indexSmallArray fs (sizeofSmallArray fs - 1)
{-# INLINE peekFrame #-}

popFrame :: forall f fs. Frames (f fs) -> Frames fs
popFrame (Frames fs) = Frames $ cloneSmallArray fs 0 (sizeofSmallArray fs - 1)
{-# INLINE popFrame #-}

indexFrame
  :: forall f fs' r. f :<# fs'
  => Frames fs'
  -> (forall fs. f fs :<<# fs' => Proxy# fs -> Frame f fs -> r)
  -> r
indexFrame (Frames fs) fn =
  ( let !idx = indexValF @f @fs' in
    assert (idx >= 0)
  $ assert (idx < sizeofSmallArray fs)
    let !f = unsafeCoerce $ indexSmallArray fs idx in
    withSubIndexF @(f fs) @fs' idx
  $ fn @fs proxy# f
  ) :: forall (fs :: FramesK). r
{-# INLINE indexFrame #-}

setFrame :: forall f fs fs'. f fs :<<# fs' => Frame f fs -> Frames fs' -> Frames fs'
setFrame f (Frames fs) = Frames $ runSmallArray do
  fs' <- thawSmallArray fs 0 (sizeofSmallArray fs)
  writeSmallArray fs' (subIndexValF @(f fs) @fs') (unsafeCoerce f)
  pure fs'

takeFrames :: forall fs fs'. fs :<<# fs' => Frames fs' -> Frames fs
takeFrames (Frames hs) =
  let len = subIndexValF @fs @fs' + 1
  in assert (len >= 0) $ assert (len <= sizeofSmallArray hs) $
    Frames $ cloneSmallArray hs 0 len
{-# INLINE takeFrames #-}

lookupFrame
  :: forall eff fs' r. eff :-> fs' -> Frames fs'
  -> (forall f fs. (eff ~ FrameEffect f, f fs :<<# fs') => Proxy# (f fs) -> Frame f fs -> r) -> r
lookupFrame (Target t) (Frames fs) f =
  ( assert (t >= 0)
  $ assert (t < sizeofSmallArray fs)
  $ with (axiom @eff @(FrameEffect f))
  $ withSubIndexF @(f fs) @fs' t
  $ f @f @fs proxy# (unsafeCoerce $ indexSmallArray fs t)
  ) :: forall (f :: FrameK) (fs :: FramesK). r
{-# INLINE lookupFrame #-}

replaceFrame
  :: forall eff fs'
   . eff :-> fs'
  -> Frames fs'
  -> (forall f fs. eff ~ FrameEffect f => Proxy# (f fs) -> Frame f fs)
  -> Frames fs'
replaceFrame (Target t) (Frames fs) f =
  ( assert (t >= 0)
  $ assert (t < sizeofSmallArray fs)
  $ with (axiom @eff @(FrameEffect f))
  $ Frames $ runSmallArray do
      fs' <- thawSmallArray fs 0 (sizeofSmallArray fs)
      writeSmallArray fs' t (unsafeCoerce $ f @f @fs proxy#)
      pure fs'
  ) :: forall (f :: FrameK) (fs :: FramesK). Frames fs

-- -- | Looks up a 'Handler' for @eff@ via the 'targets' indirection vector.
-- withHandler
--   :: forall eff effs fs' r. eff :< effs
--   => effs :->> fs' -> Frames fs'
--   -> (forall i fs. 'PROMPT eff i fs :<<! fs' => Proxy# i -> Proxy# fs -> Handler eff i fs -> r) -> r
-- withHandler (Targets ts) (Frames fs) f =
--   let idx = indexByteArray ts (indexVal @eff @effs)
--   in case unsafeCoerce $ indexSmallArray fs idx of
--     (h :: Handler eff i fs) -> with (axiomC @('PROMPT eff i fs :<<! fs')) $
--       f (proxy# @_ @i) (proxy# @_ @fs) h
-- {-# INLINE withHandler #-}

run :: forall a. Eff '[] a -> a
run (Eff m) = m
  (\v (_ :: Context '[] effss fs) -> with (topsRoot @a @fs) v)
  (Context (RootTargets noTargets) rootFrames)
{-# INLINE run #-}

instance Functor (Eff effs) where
  fmap f (Eff m) = Eff \k -> m \a -> k (f a)
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff \k -> k a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff m >>= f = Eff \k (ctx1 :: Context effs effss1 fs1) ->
    m (\a (ctx2 :: Context effs effss2 fs2) ->
        unEff (f a)
              (\b (ctx3 :: Context effs effss3 fs3) ->
                with (topsTrans @fs1 @fs2 @fs3) $ k b ctx3)
              ctx2)
      ctx1
  {-# INLINE (>>=) #-}

lift :: forall effs effs'. effs :<< effs' => Eff effs ~> Eff effs'
lift (Eff m) = Eff \k (Context tss fs) ->
  -- Note: we could save some allocation and residency here by representing targets as a byte array
  -- + an offset, where 'lift' simply increments the offset (and returning decrements it). However,
  -- it isn’t clear whether or not that’s a win without benchmarking.
  let !ctx = Context (PushTargets (dropTargets $ peekTargets tss) tss) fs
  in m (\a (Context tss' fs') -> k a $! Context (popTargets tss') fs') ctx

-- | Like 'lift', but restricted to introducing a single additional effect in the result. This is
-- behaviorally identical to just using 'lift', but the restricted type can produce better type
-- inference.
lift1 :: forall eff effs. Eff effs ~> Eff (eff ': effs)
lift1 = lift
{-# INLINE lift1 #-}

liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff m) = Eff \k (Context tss fs :: Context effs' effss' fs') ->
  withHandling @eff @effs' (peekTargets tss) \(_ :: Proxy# effss) ->
  indexFrame @('PROMPT eff effs i effss) fs \_ h ->
    let !ts = weakenTargets $ hTargets h
        !ctx = Context (PushTargets ts tss) fs
    in m (\a (Context tss' fs') -> k a $! Context (popTargets tss') fs') ctx

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \k ctx@(Context tss fs :: Context effs1 effss1 fs1) ->
  with (handles e) $
  lookupFrame (lookupTarget @eff $ peekTargets tss) fs \(_ :: Proxy# (f2 fs2)) h ->
  withHandlesImpliesPrompt @eff @f2 \(_ :: Proxy# ('PROMPT eff effs2 i effss2)) ->
  reflectHandling @eff @effs2 @i @effss2 @fs2 @effs @fs1 $
    unEff (hSend h e) k ctx

abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
abort a = Eff \_ (Context tss (fs :: Frames fs')) ->
  withHandling @eff @effs' (peekTargets tss) \(_ :: Proxy# effss) ->
  indexFrame @('PROMPT eff effs i effss) fs \(_ :: Proxy# fs) h ->
  withWeakenSubIndex @('PROMPT eff effs i effss) @fs @fs' $
  with (rootsEq @fs @fs') $
    hCont h a $! Context (hTargetss h) (takeFrames fs)

-- shift
--   :: forall eff effs i effs' a. Handling eff effs i effs'
--   => ((a -> Eff effs i) -> Eff effs i) -> Eff effs' a
-- shift f = Eff \kn (Context tssn fsn :: Context effsn effssn fsn) ->
--   withHandling @eff @effs' (peekTargets tssn) \(_ :: Proxy# effss0) ->
--   indexFrame @('PROMPT eff effs i effss0) fsn \(_ :: Proxy# fs0) !h0 ->
--   withWeakenSubIndex @('PROMPT eff effs i effss0) @fs0 @fsn $
--   with (rootsEq @fs0 @fsn)
--     let m :: Eff effs i
--         m = f \a -> Eff \k1 (Context tss1 fs1 :: Context effs1 effss1 fs1) ->
--           -- If we get here, it’s time to do the continuation dance. We start by copying the local
--           -- frames from the captured continuation onto the current stack.
--           _
--     in unEff m (hCont h0) $! Context (hTargetss h0) (takeFrames fsn)

-- shift f = mkEff \(_ :: Proxy# fsn) kn tsn fsn ->
--   withHandlingTargets' @eff tsn \(_ :: Proxy# fs0) ts0 _ ->
--   with (eraseSub @('PROMPT eff i fs0) @fsn) $
--   with (rootsEq @('PROMPT eff i fs0) @fsn) $
--   withWeakenSubIndex @('PROMPT eff i) @fs0 @fsn
--     let !h0 = indexFrame @('PROMPT eff i fs0) fsn
--
--         m :: Eff effs i
--         m = f \a -> mkEff \(_ :: Proxy# fs1) k1 ts1 fs1 ->
--           -- Here’s where all the magic happens. The continuation `kn` is wired to run the current
--           -- prompt to completion, then pop it and call the parent frame’s continuation, `hCont`.
--           -- This process happens transitively, eventually reaching the root continuation.
--           --
--           -- To capture a portion of the continuation, all we have to do is “redirect” the return
--           -- from a given prompt by replacing its `hCont` with a continuation that actually goes
--           -- somewhere else. In this case, we replace it with `k1`, so it actually jumps into
--           -- whatever computation `f` places the resulting `Eff` computation in.
--           --
--           -- That is exactly what we want, but unfortunately, the current type used for the
--           -- continuation inside `Eff` doesn’t really understand the effect of this redirection.
--           -- The continuation expects `hCont` to still be a continuation into the underlying frame,
--           -- one that eventually returns `R fsn`.
--           --
--           -- Rather than plumb this information through properly, we just cheat and call
--           -- `unsafeCoerce`. This actually is safe to the best of my knowledge, but it’s still
--           -- troubling. I would love to find a way to capture this in the type system, but I haven’t
--           -- come up with anything workable yet.
--           with (axiom @(R fs0) @(R fs1)) $ -- Evil!! Depends on the aforementioned redirection.
--             let k :: i -> Frames fs -> R fs1
--                 k a _ = k1 a fs1 -- This does the redirection, dropping the old frames completely.
--                 !h0' = h0 { hCont = k }
--             in kn a $! setFrame @('PROMPT eff i fs0) h0' fsn
--
--     in unEff m (hCont h0) ts0 $! takeFrames @fs0 fsn
--
-- getC :: forall s effs. Cell s :< effs => Eff effs s
-- getC = Eff \k ts fs ->
--   lookupFrame (lookupTarget @(Cell s) ts) fs \(_ :: Proxy# f) _ !s ->
--     with (decomposeCell @s @f) k s fs
--
-- putC :: forall s effs. Cell s :< effs => s -> Eff effs ()
-- putC s = mkEff \(_ :: Proxy# fs) k ts fs ->
--   k () $! replaceFrame (lookupTarget @(Cell s) ts) fs \(_ :: Proxy# f) _ ->
--     with (decomposeCell @s @f) s
--
-- runCell :: forall s effs. s -> Eff (Cell s ': effs) ~> Eff effs
-- runCell s (Eff m) = mkEff \(_ :: Proxy# fs) k ts fs ->
--   withLengthOf fs $
--   with (weakenSub @fs @('CELL s) @fs)
--     let !ts' = pushTarget (newTarget @('CELL s)) (weakenTargets ts)
--         !fs' = pushFrame @('CELL s) s fs
--     in m (\a fs' -> k a $! popFrame fs') ts' fs'

class Handling (eff :: Effect) (effs :: [Effect]) (i :: Type) (effs' :: [Effect]) | eff effs' -> i effs where
  handlerIndexVal :: Int

withHandling
  :: forall eff effs' fs effs i r
   . Handling eff effs i effs'
  => effs' :->> fs
  -- ^ Not actually used, but serves as a proof that we’re in a context where the 'Handling'
  -- constraint applies.
  -> (forall effss. 'PROMPT eff effs i effss :<# fs => Proxy# effss -> r)
  -> r
withHandling !_ f =
  ( withIndexF @('PROMPT eff effs i effss) @fs (handlerIndexVal @eff @effs @i @effs')
  $ f @effss proxy#
  ) :: forall (effss :: [[Effect]]). r
{-# INLINE withHandling #-}

newtype WithHandling eff effs i effs' r = WithHandling (Handling eff effs i effs' => r)
reflectHandlerIndex :: forall eff effs i effs' r. Int -> (Handling eff effs i effs' => r) -> r
reflectHandlerIndex n x = unsafeCoerce (WithHandling @eff @effs @i @effs' x) $! n
{-# INLINE reflectHandlerIndex #-}

reflectHandling
  :: forall eff effs i effss fs effs' fs' r. 'PROMPT eff effs i effss fs :<<# fs'
  => (Handling eff effs i effs' => r) -> r
reflectHandling =
  reflectHandlerIndex @eff @effs @i @effs' (subIndexValF @('PROMPT eff effs i effss fs) @fs')
{-# INLINE reflectHandling #-}

handle
  :: forall eff a effs. Handles eff
  => (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f (Eff m) = Eff \k0 (Context tss0 fs0 :: Context effs effss0 fs0) -> withLengthOf fs0
  let k2 :: forall fs2. 'PROMPT eff effs a effss0 fs0 ^~ fs2
         => a -> Context (eff ': effs) '[] fs2 -> R fs2
      k2 a (Context tss2 fs2) = withTopFramesEq @('PROMPT eff effs a effss0) @fs0 @fs2
        let !h2 = peekFrame fs2
        in hCont h2 a $! Context (hTargetss h2) (popFrame fs2)

      !tss0' = weakenTargetss tss0
      !ts1 = pushTarget (newTarget @('PROMPT eff effs a effss0)) $ peekTargets tss0'
      !fs1 = pushFrame @('PROMPT eff effs a effss0) (Handler ts1 tss0 f k0) fs0
  in m k2 $! Context (RootTargets ts1) fs1

-- class Swizzle effs effs' where
--   swizzleTargets :: effs' :->> fs -> effs :->> fs
-- instance {-# INCOHERENT #-} effs :<< effs' => Swizzle effs effs' where
--   swizzleTargets = dropTargets
--   {-# INLINE swizzleTargets #-}
-- instance Swizzle '[] effs where
--   swizzleTargets _ = noTargets
--   {-# INLINE swizzleTargets #-}
-- instance (eff :< effs', Swizzle effs effs') => Swizzle (eff ': effs) effs' where
--   swizzleTargets ts = pushTarget (lookupTarget @eff ts) $! swizzleTargets @effs ts
--
-- -- | A magician hands you a deck of cards.
-- --
-- -- “Take some cards off the top,” she tells you, “then put them back in any order you like.”
-- --
-- -- That’s what 'swizzle' does. If you picture the list of effects @effs@ like a deck of cards,
-- -- 'swizzle' allows you to rearrange it arbitrarily, so long as all the cards you started with are
-- -- still /somewhere/ in the deck when you’re finished. In fact, 'swizzle' is even more powerful than
-- -- that, as you may also add entirely new cards into the deck, as many as you please! You just can’t
-- -- take any cards out.
-- --
-- -- As it happens, the metaphor is apt for more reason than one, because 'swizzle' is slightly
-- -- magical. Under the hood, it tries its absolute best to figure out what you mean. Usually it does
-- -- a pretty good job, but sometimes it doesn’t get it quite right, and you may receive a rather
-- -- mystifying type error. In that case, fear not: all you need to do is offer it a little help by
-- -- adding some type annotations (or using @TypeApplications@).
-- swizzle :: Swizzle effs effs' => Eff effs ~> Eff effs'
-- swizzle (Eff m) = Eff \k ts -> m k (swizzleTargets ts)
-- {-# INLINE swizzle #-}

-}
