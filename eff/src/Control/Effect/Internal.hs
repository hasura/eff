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

-- | If one stack of frames is contained within the other, their root frames must be equal.
rootsEq :: forall fs1 fs2. fs1 :<<# fs2 => 'ROOT (S fs1) (R fs1) :~: 'ROOT (S fs2) (R fs2)
rootsEq = reifySubIndexF @fs1 @fs2 `seq` axiom
{-# INLINE rootsEq #-}

type FrameEffect :: FrameK -> Effect
type family FrameEffect f where
  FrameEffect ('CELL s) = Cell s
  FrameEffect ('PROMPT eff _ _ _) = eff


-- | A proof that the /top frames/ of two 'FramesK' types are equal, up to the topmost prompt. If
-- there are no prompts, they must be completely identical.
--
-- Morally, this type is a GADT of the following shape:
--
-- @
-- data fs1 ^~ fs2 where
--   Roots :: 'ROOT s r ^~ 'ROOT s r
--   Cells :: fs1 ^~ fs2 -> 'CELL s fs1 ^~ 'CELL s fs2
--   Prompts :: 'PROMPT eff effs i effss fs1 ^~ 'PROMPT eff effs i effss fs2
-- @
--
-- However, if it were defined that way, it would have a runtime overhead, albeit a small one. This
-- is silly, since we’re only using it as a proof term for type safety purposes, and it isn’t worth
-- paying /any/ cost for. Therefore, it is actually defined as a zero-representation type, which is
-- guaranteed to be erased, and pattern synonyms are used to fake GADT constructors.
--
-- One consequence of this is that it’s illegal to actually branch on a value of this type, as there
-- is no runtime information available that can be used to choose the correct branch. The first
-- branch will therefore always be chosen, breaking type system soundess in the process, since the
-- assumption made by the first branch may not actually hold! (That is, only one of the other
-- branch’s assumptions hold.) Sadly, defining the pattern synonyms in a way that enforces this
-- appears to lose exhaustiveness checking, so this is not enforced.
type (^~) :: FramesK -> FramesK -> TYPE ('TupleRep '[])
newtype fs1 ^~ fs2 = UnsafeTopsEq Void#
{-# COMPLETE Roots, Cells, Prompts #-}

pattern Roots :: forall fs1 fs2. () => forall s r. (fs1 ~ 'ROOT s r, fs2 ~ 'ROOT s r) => fs1 ^~ fs2
pattern Roots <-
  ((\_ -> (# unsafeRefl# void#, unsafeRefl# void# #)
       :: forall s r. (# fs1 ~# 'ROOT s r, fs2 ~# 'ROOT s r #))
   -> (# Refl#, Refl# #))
  where Roots = UnsafeTopsEq void#

pattern Cells
  :: forall fs1 fs2. () => forall s fs3 fs4
   . (fs1 ~ 'CELL s fs3, fs2 ~ 'CELL s fs4) => fs3 ^~ fs4 -> fs1 ^~ fs2
pattern Cells a <-
  ((\_ -> (# unsafeRefl# void#, unsafeRefl# void#, UnsafeTopsEq void# #)
       :: forall s fs3 fs4. (# fs1 ~# 'CELL s fs3, fs2 ~# 'CELL s fs4, fs3 ^~ fs4 #))
  -> (# Refl#, Refl#, a #))
  where Cells _ = UnsafeTopsEq void#

pattern Prompts
  :: forall fs1 fs2. () => forall eff effs i effss fs3 fs4
   . (fs1 ~ 'PROMPT eff effs i effss fs3, fs2 ~ 'PROMPT eff effs i effss fs4) => fs1 ^~ fs2
pattern Prompts <-
  ((\_ -> (# unsafeRefl# void#, unsafeRefl# void# #)
       :: forall eff effs i effss fs3 fs4. (# fs1 ~# 'PROMPT eff effs i effss fs3, fs2 ~# 'PROMPT eff effs i effss fs4 #))
  -> (# Refl#, Refl# #))
  where Prompts = UnsafeTopsEq void#

topsRefl :: fs1 ~ fs2 => fs1 ^~ fs2
topsRefl = UnsafeTopsEq void#
{-# INLINE topsRefl #-}

topsTrans :: fs1 ^~ fs2 -> fs2 ^~ fs3 -> fs1 ^~ fs3
topsTrans _ _ = UnsafeTopsEq void#
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
instance (effs2 ~ (eff ': effs3), effs1 :<< effs3) => effs1 :<< effs2 where
  reifySubIndex = reifySubIndex @effs1 @effs3 + 1
  {-# INLINE reifySubIndex #-}

type (:<<:) :: [Effect] -> [Effect] -> TYPE 'IntRep
newtype effs1 :<<: effs2 = SubIndex# Int#

reifySubIndex# :: forall effs1 effs2. effs1 :<< effs2 => effs1 :<<: effs2
reifySubIndex# = let !(I# idx) = reifySubIndex @effs1 @effs2 in SubIndex# idx

reflectSubIndex# :: forall effs1 effs2 r. effs1 :<<: effs2 -> (effs1 :<< effs2 => r) -> r
reflectSubIndex# (SubIndex# idx) = reflectDict @(effs1 :<< effs2) (I# idx)

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

withWeakenSubIndex :: forall f fs1 fs2 r. f fs1 :<<# fs2 => (fs1 :<<# fs2 => r) -> r
withWeakenSubIndex = reflectDict @(fs1 :<<# fs2) (reifySubIndexF @(f fs1) @fs2 - 1)
{-# INLINE withWeakenSubIndex #-}

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
newtype Context effs effss fs = Context#
  (# effs :->> fs, effss :=>> fs, (effs ': effss) :~>> fs, Frames# fs #)
pattern Context :: effs :->> fs -> effss :=>> fs -> (effs ': effss) :~>> fs -> Frames fs -> Context effs effss fs
pattern Context a b c d <- Context# (# a, b, c, (BoxFrames -> d) #)
  where Context a b c (BoxFrames d) = Context# (# a, b, c, d #)
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

-- | The representation of the frame @f@ above a stack of underlying frames @fs@.
type Frame :: FrameK -> FramesK -> Type
data Frame f fs where
  Cell :: ~s -> Frame ('CELL s) fs
  Prompt ::
    { pCont :: forall fs2. fs ^~ fs2 -> i -> Context effs effss fs2 -> ST (S fs2) (R fs2)
    -- ^ The continuation between this prompt and the parent prompt.
    , pHandler :: forall effs'. Handling# eff effs i effs' -> eff (Eff effs') ~> Eff effs'
    , pTargets :: (eff ': effs) :->> 'PROMPT eff effs i effss fs
    , pTargetss :: (effs ': effss) :=>> fs
    , pRemappings :: (effs ': effss) :~>> fs
    } -> Frame ('PROMPT eff effs i effss) fs

-- -------------------------------------------------------------------------------------------------


{- The arrow zoo:

  * eff   :->  fs — target indirection index
  * effs  :->> fs — target indirection vector
  * effss :=>> fs — target indirection stack
  * effs  :~>> fs — target remapping stack

-}

type (:->) :: Effect -> FramesK -> Type
newtype eff :-> fs = Target { unTarget :: Int }

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

-- | A /target remapping stack/, which records changes to the target indirection stack. The
-- remapping stack is saved whenever a continuation is captured, and it is “replayed” when the
-- continuation is restored to rebuild a new target indirection stack for a new set of frames.
type (:~>>) :: [[Effect]] -> FramesK -> Type
data effss :~>> fs where
  Run :: '[effs] :~>> fs
  Lift :: effs1 :<<: effs2
       -> (effs2 ': effss) :~>> fs
       -> (effs1 ': effs2 ': effss) :~>> fs
  LiftH :: Handling# eff effs i effs'
        -> (effs' ': effss) :~>> fs
        -> ((eff ': effs) ': effs' ': effss) :~>> fs

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

pushFrame :: DebugCallStack => Frame f fs -> Frames fs -> ST (S fs) (Frames (f fs))
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

popFrame :: DebugCallStack => Frames (f fs) -> ST (S fs) (Frame f fs, Frames fs)
popFrame (Frames len fs) = do
  -- Note that we never resize the frames stack when popping, only when pushing, so the size of the
  -- frames stack will never decrease. Theoretically, if someone created a giant frames stack very
  -- briefly, then executed a long-lived computation with a much smaller stack, this would leak
  -- memory. However, such a usage pattern seems unlikely, so for now, we never decrease the size of
  -- the stack.
  Any f <- readSmallArray fs (len - 1)
  writeSmallArray fs len null#
  pure (f, Frames (len - 1) fs)

dropFrames :: forall fs1 fs2. (DebugCallStack, fs1 :<<# fs2) => Frames fs2 -> ST (S fs2) (Frames fs1)
dropFrames (Frames len1 fs) = with (rootsEq @fs1 @fs2) do
  let len2 = reifySubIndexF @fs1 @fs2
  assertM $ len2 <= len1
  for_ [len2..len1-1] \idx ->
    writeSmallArray fs idx null#
  pure $ Frames len2 fs

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
-- remappings

popRemapping :: (effs1 ': effs2 ': effss) :~>> fs -> (effs2 ': effss) :~>> fs
popRemapping (Lift _ trs) = trs
popRemapping (LiftH _ trs) = trs

-- -------------------------------------------------------------------------------------------------
-- core Eff operations

instance Functor (Eff effs) where
  fmap f (Eff m) = Eff \k -> m \tops a -> k tops (f a)
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff \k -> k topsRefl a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff m >>= f = Eff \k -> m \tops1 a -> unEff (f a) \tops2 -> k (topsTrans tops1 tops2)
  {-# INLINE (>>=) #-}

run :: Eff '[] a -> a
run (Eff m) = runST do
  fs <- newEmptyFrames
  m (\Roots v _ -> pure v) (Context noTargets NoTargetss Run fs)

lift :: effs1 :<< effs2 => Eff effs1 ~> Eff effs2
lift (Eff m) = Eff \k (Context ts1 tss1 trs1 fs1) ->
  m (\tops a (Context _ (PushTargets ts2 tss2) (popRemapping -> trs2) fs2) ->
       k tops a (Context ts2 tss2 trs2 fs2))
    (Context (dropTargets ts1) (PushTargets ts1 tss1) (Lift reifySubIndex# trs1) fs1)

-- | Like 'lift', but restricted to introducing a single additional effect in the result. This is
-- behaviorally identical to just using 'lift', but the restricted type can produce better type
-- inference.
lift1 :: forall eff effs. Eff effs ~> Eff (eff ': effs)
lift1 = lift
{-# INLINE lift1 #-}

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

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \k ctx@(Context ts _ _ fs) ->
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
handle f (Eff m) = Eff \k1 (Context ts1 tss1 trs1 fs1 :: Context effs effss1 fs1) ->
  withDepthOf fs1 do
    let f1 :: Frame ('PROMPT eff effs a effss1) fs1
        f1 = Prompt
          { pCont = k1
          , pHandler = \n e -> reflectHandling# n $ f e
          , pTargets = ts2
          , pTargetss = PushTargets ts1 tss1
          , pRemappings = trs1
          }

        ts2 :: (eff ': effs) :->> 'PROMPT eff effs a effss1 fs1
        ts2 = pushTarget (newTarget @('PROMPT eff effs a effss1)) (weakenTargets ts1)

        k2 :: forall fs2. 'PROMPT eff effs a effss1 fs1 ^~ fs2
           -> a -> Context (eff ': effs) '[] fs2 -> ST (S fs2) (R fs2)
        k2 Prompts a (Context _ _ _ ffs3) = do
          (f3, fs3) <- popFrame ffs3
          let !(PushTargets ts3 tss3) = pTargetss f3
              !trs3 = pRemappings f3
          pCont f3 topsRefl a (Context ts3 tss3 trs3 fs3)

    fs2 <- pushFrame f1 fs1
    m k2 (Context ts2 NoTargetss Run fs2)

liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff m) = Eff \k (Context ts1 tss1 trs1 fs1) ->
  withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
  lookupFrame @('PROMPT eff effs i effss) fs1 \_ p ->
    m (\tops a (Context _ (PushTargets ts2 tss2) (popRemapping -> trs2) fs2) ->
         k tops a (Context ts2 tss2 trs2 fs2))
      (Context (weakenTargets $ pTargets p) (PushTargets ts1 tss1) (LiftH reifyHandling# trs1) fs1)

abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
abort a = Eff \_ (Context ts1 _ _ (fs1 :: Frames fs1)) ->
  withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
  lookupFrame @('PROMPT eff effs i effss) fs1 \(_ :: Proxy# fs2) p ->
  withWeakenSubIndex @('PROMPT eff effs i effss) @fs2 @fs1 $
  with (rootsEq @fs2 @fs1) do
    let !(PushTargets ts2 tss2) = pTargetss p
        !trs2 = pRemappings p
    fs2 <- dropFrames fs1
    pCont p topsRefl a (Context ts2 tss2 trs2 fs2)

-- shift
--   :: forall eff effs i effs' a. Handling eff effs i effs'
--   => ((a -> Eff effs i) -> Eff effs i) -> Eff effs' a
-- shift f = Eff \k1 (Context ts1 tss1 (fs1 :: Frames fs1)) ->
--   withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
--   lookupFrame @('PROMPT eff effs i effss) fs1 \(_ :: Proxy# fs2) p ->
--   withWeakenSubIndex @('PROMPT eff effs i effss) @fs2 @fs1 $
--   with (rootsEq @fs2 @fs1) do
--     let m :: Eff effs i
--         m = f \a -> Eff \k2 (Context ts3 tss3 fs3) ->
--           _ -- k1 topsRefl a (Context )
--
--         !(PushTargets ts2 tss2) = pTargetss p
--     fs2 <- dropFrames fs1
--     unEff m (pCont p) (Context ts2 tss2 fs2)

-- -------------------------------------------------------------------------------------------------
