-- {-# OPTIONS_GHC -fno-max-relevant-binds #-}
-- {-# OPTIONS_GHC -fmax-relevant-binds=20 #-}
{-# OPTIONS_GHC -Wno-unused-imports -Wno-redundant-constraints -Wno-unused-foralls #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnboxedSums #-}

module Control.Effect.Internal where

import qualified Control.Effect.Internal.Continuation as IO
import qualified Control.Exception as IO

import Control.Exception (Exception)
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Natural (type (~>))
import Data.Coerce
import Data.Kind (Constraint, Type)
import Data.Foldable
import Data.Functor
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (Any, Int(..), Int#, Proxy#, RealWorld, RuntimeRep(..), SmallMutableArray#, State#, TYPE, Void#, (+#), proxy#, runRW#, void#)
import GHC.TypeLits (ErrorMessage(..), Nat, TypeError)
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafeDupablePerformIO)

import Control.Effect.Internal.Debug
import Control.Effect.Internal.Equality
import Control.Effect.Internal.PrimArray
import Control.Effect.Internal.SmallArray

-- -------------------------------------------------------------------------------------------------

letT :: (Proxy# a -> r) -> r
letT f = f proxy#
{-# INLINE letT #-}

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

type DictRep :: Constraint -> Type
type family DictRep c

type WithDict :: Constraint -> Type -> Type
newtype WithDict c r = WithDict { unWithDict :: c => r }

reifyDict :: forall c. c => DictRep c
reifyDict = unWithDict @c @(DictRep c) (unsafeCoerce (id @(DictRep c)))
{-# INLINE reifyDict #-}

reflectDict :: forall c r. DictRep c -> (c => r) -> r
reflectDict d x = unsafeCoerce (WithDict @c @r x) $! d
{-# INLINE reflectDict #-}

data Dict' c = c => Dict'

-- | Reifies a typeclass dictionary as a value. The main advantage to this is that it can be
-- UNPACKed when stored in another datatype.
newtype Dict c = DictRep (DictRep c)
pattern Dict :: forall c. () => c => Dict c
pattern Dict <- DictRep ((\d -> reflectDict @c @(Dict' c) d Dict') -> Dict')
  where Dict = DictRep (reifyDict @c)
{-# COMPLETE Dict #-}

instance With (Dict c) where
  type WithC (Dict c) = c
  with Dict x = x
  {-# INLINE with #-}

-- -- -------------------------------------------------------------------------------------------------
--
-- type IsPrefixOf :: [k] -> [k] -> TYPE ('TupleRep '[])
-- newtype IsPrefixOf xs ys = UnsafeIsPrefixOf# Void#
-- {-# COMPLETE IsPrefixOfNil, IsPrefixOfCons #-}
--
-- pattern IsPrefixOfNil :: IsPrefixOf '[] xs
-- pattern IsPrefixOfNil <- _
--   where IsPrefixOfNil = UnsafeIsPrefixOf# void#
--
-- pattern IsPrefixOfCons
--   :: forall x xs ys. () => forall zs. ys ~ (x ': zs) => IsPrefixOf xs zs -> IsPrefixOf (x ': xs) ys
-- pattern IsPrefixOfCons pfx <-
--   ((\_ -> (# unsafeRefl# void#, UnsafeIsPrefixOf# void# #)
--        :: forall zs. (# ys ~# (x ': zs), IsPrefixOf xs zs #)
--    ) -> (# Refl#, pfx #))
--   where IsPrefixOfCons _ = UnsafeIsPrefixOf# void#

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

-- type Depth :: [FrameK] -> Constraint
-- class Depth fs where
--   reifyDepth :: Int
-- instance Depth '[] where
--   reifyDepth = 0
--   {-# INLINE reifyDepth #-}
-- instance Depth fs => Depth (f ': fs) where
--   reifyDepth = reifyDepth @fs + 1
--   {-# INLINE reifyDepth #-}
--
-- type (:<#) :: FrameK -> [FrameK] -> Constraint
-- class f :<# fs where
--   reifyIndexF :: Int
-- instance {-# OVERLAPPING #-} Depth (f ': fs) => f :<# (f ': fs) where
--   reifyIndexF = reifyDepth @(f ': fs) - 1
--   {-# INLINE reifyIndexF #-}
-- instance f :<# fs => f :<# (f' ': fs) where
--   reifyIndexF = reifyIndexF @f @fs
--   {-# INLINE reifyIndexF #-}
--
-- type (:<<#) :: [FrameK] -> [FrameK] -> Constraint
-- class fs1 :<<# fs2 where
--   reifySubIndexF :: Int
-- instance {-# OVERLAPPING #-} Depth fs => fs :<<# fs where
--   reifySubIndexF = reifyDepth @fs - 1
--   {-# INLINE reifySubIndexF #-}
-- instance (fs2 ~ (f ': fs3), fs1 :<<# fs3) => fs1 :<<# fs2 where
--   reifySubIndexF = reifySubIndexF @fs1 @fs3
--   {-# INLINE reifySubIndexF #-}

type instance DictRep (eff :< effs) = Int
type instance DictRep (effs1 :<< effs2) = Int
-- type instance DictRep (Depth fs) = Int
-- type instance DictRep (f :<# fs) = Int
-- type instance DictRep (fs1 :<<# fs2) = Int

-- withWeakenSubIndex :: forall f fs1 fs2 r. (f ': fs1) :<<# fs2 => (fs1 :<<# fs2 => r) -> r
-- withWeakenSubIndex = reflectDict @(fs1 :<<# fs2) (reifySubIndexF @(f ': fs1) @fs2 - 1)
-- {-# INLINE withWeakenSubIndex #-}

-- -------------------------------------------------------------------------------------------------

type Effect = (Type -> Type) -> Type -> Type

-- data FrameK
--   = CELL Type
--   | PROMPT Effect [Effect] Type [[Effect]]
--
-- type FrameEffect :: FrameK -> Effect
-- type family FrameEffect f where
--   FrameEffect ('CELL s) = Cell s
--   FrameEffect ('PROMPT eff _ _ _) = eff

-- | The primitive state pseudo-effect, which provides access to a single cell of mutable state of
-- type @s@. Unlike real effects, 'Cell' only has one handler, 'runCell'. Users should not use
-- 'Cell' directly, but should instead use the ordinary 'State' effect; the default handler for
-- 'State' is internally implemented as a small wrapper around 'Cell'.
type Cell :: Type -> Effect
type role Cell representational _ _
data Cell s :: Effect

type family Handles eff :: Constraint where
  Handles (Cell s) = NoHandling Cell (Cell s)
  Handles _ = ()
type family NoHandling c eff where
  NoHandling c eff = TypeError
    ( 'Text "no instance for ‘Handles (" ':<>: 'ShowType eff ':<>: 'Text ")’;"
    ':$$: 'Text "  " ':<>: 'ShowType c ':<>: 'Text " is a primitive effect and cannot be handled" )

-- | Primitive effects are uninhabited, so we can obtain a proof of 'Handles' by forcing an effect
-- value.
handles :: eff m a -> Handles eff :~: (() :: Constraint)
handles !_ = axiom
{-# INLINE handles #-}

-- withHandlesImpliesPrompt
--   :: forall f eff m a r. (Handles eff, eff ~ FrameEffect f)
--   => (forall effs i effss. f ~ 'PROMPT eff effs i effss => Proxy# ('PROMPT eff effs i effss) -> r)
--   -> r
-- withHandlesImpliesPrompt k =
--   ( with (axiom @f @('PROMPT eff effs i effss))
--   $ k @effs @i @effss proxy#
--   ) :: forall (effs :: [Effect]) (i :: Type) (effss :: [[Effect]]). r

-- -------------------------------------------------------------------------------------------------

newtype Eff effs a = Eff { unEff :: PromptId -> Targets effs -> IO a }

-- -- | This wrapper type is necessary to get the 'v:Eff' pattern synonym to typecheck, as otherwise it
-- -- would require impredicative polymorphism.
-- --
-- -- FIXME: Not needed anymore, no longer impredicative!
-- newtype EffAsIO effs a = EffAsIO (Context effs -> IO (Context effs, a))
--
-- -- | A pattern synonym that makes 'Eff' look like it’s defined in terms of 'IO' rather than in terms
-- -- of 'State#', since the former is easier to work with (and the optimizer will remove the
-- -- wrapping/unwrapping).
-- pattern Eff :: (Context effs -> IO (Context effs, a)) -> Eff effs a
-- pattern Eff { unEff } <- ((\(Eff# f) -> EffAsIO \ctx -> primitive \s1 -> case f ctx s1 of (# s2, ctx2, a #) -> (# s2, (ctx2, a) #)) -> EffAsIO unEff)
--   where Eff f = Eff# \ctx1 s1 -> case internal (f ctx1) s1 of (# s2, (ctx2, a) #) -> (# s2, ctx2, a #)
-- {-# COMPLETE Eff #-}
--
-- type Context :: [Effect] -> Type
-- data Context effs = Context {-# UNPACK #-} Int {-# UNPACK #-} (Targets effs)
--   -- (TargetsStack effss fs) {-# UNPACK #-} (Frames fs)

-- type Context :: [Effect] -> [[Effect]] -> Type
-- data Context effs effss = forall fs. Context
--   {-# UNPACK #-} (Targets effs fs) (TargetsStack effss fs) {-# UNPACK #-} (Frames fs)
--
-- type Frames :: [FrameK] -> Type
-- data Frames fs = Frames {-# UNPACK #-} Int {-# UNPACK #-} (SmallMutableArray RealWorld Any)
--
-- type Frame :: FrameK -> [FrameK] -> Type
-- type family Frame f fs where
--   Frame ('CELL s) _ = s
--   Frame ('PROMPT eff effs i effss) fs = Prompt eff effs i effss fs

data Prompt eff effs i = Prompt
  { pHandler :: forall effs'. Handling# eff effs i effs' -> eff (Eff effs') ~> Eff effs'
  }

type Targets :: [Effect] -> Type
type role Targets nominal
newtype Targets effs = Targets (SmallArray Any)

-- type Target :: Effect -> [FrameK] -> Type
-- newtype Target eff fs = Target Int
--
-- type Targets :: [Effect] -> [FrameK] -> Type
-- newtype Targets effs fs = Targets (PrimArray Int)

-- type TargetsStack :: [[Effect]] -> [FrameK] -> Type
-- data TargetsStack effss fs where
--   EmptyTargetsStack :: TargetsStack '[] fs
--   PushTargets ::
--     { peekTargets :: {-# UNPACK #-} Targets effs fs
--     , popTargets :: TargetsStack effss fs
--     } -> TargetsStack (effs ': effss) fs

data AbortException = AbortException {-# UNPACK #-} Int ~Any
instance Show AbortException where
  show (AbortException _ _) = "AbortException"
instance Exception AbortException

newtype PromptId = PromptId# Int#
pattern PromptId :: Int -> PromptId
pattern PromptId{ unPromptId } <- PromptId# (I# -> unPromptId)
  where PromptId (I# n) = PromptId# n

newtype Winder effs1 effs2 a b = Winder
  { winder :: PromptId -> Targets effs1 -> IO (Targets effs2, Unwinder effs1 effs2 a b) }

data Unwinder effs1 effs2 a b = Unwinder
  { returnUnwinder :: a -> IO b
  , abortUnwinder :: IO ()
  , captureUnwinder :: IO (Winder effs1 effs2 a b) }
-- TODO: Make Winder/Unwinder operate directly on State# threads and make Unwinder an unboxed tuple
-- to ensure wind doesn’t pass closures.

data Request effs1 a
  = Return ~a
  | forall b effs2 c. Capture
      PromptId
      -- ^ The prompt we’re capturing up to.
      (b -> Eff effs1 (Request effs1 a))
      -- ^ The continuation up to this prompt.
      ((b -> Eff effs2 c) -> Eff effs2 c)
      -- ^ The metacontinuation.
-- TODO: Make continuation primops levity-polymorphic so we can use an unboxed sum type for Request.

-- | The primitive way to push a prompt.
wind :: forall effs1 effs2 a b. Winder effs1 effs2 a b -> Eff effs2 (Request effs2 a) -> Eff effs1 b
wind Winder{ winder } (Eff m) = Eff \pid1 ts1 -> do
  -- Start by applying the winder.
  let pid2 = PromptId (unPromptId pid1 + 1)
  (ts2, Unwinder{ returnUnwinder, captureUnwinder }) <- winder pid2 ts1
  -- Push a new prompt frame and invoke the delimited computation.
  IO.reset (m pid2 ts2) >>= \case
    -- Normal return; call the unwinder and return the result.
    Return a -> returnUnwinder a
    -- Someone called shift, so we’re capturing the continuation.
    Capture target k1 (f :: (c -> Eff effs3 d) -> Eff effs3 d) -> do
      -- Start by calling the capture unwinder.
      rewinder <- captureUnwinder
      -- Compose the continuation with the rewinder.
      let !k2 = wind rewinder . k1
      if unPromptId target == unPromptId pid2
        -- We’re capturing up to this prompt, so we’re done unwinding; invoke the metacontinuation.
        then with (axiom @effs1 @effs3) $ with (axiom @b @d) $ unEff (f k2) pid1 ts1
        -- We’re capturing up to a parent prompt, so capture the next continuation slice.
        else IO.shift \k# -> do
          -- Extend the continuation up to this prompt by composing it with the continuation up to
          -- the next prompt.
          let k3 b = Eff \pid3 ts3 -> IO.applyContinuation k# $ unEff (k2 b) pid3 ts3
          pure $! Capture target k3 f

-- -- -------------------------------------------------------------------------------------------------
-- -- frames
--
-- -- | A restricted form of 'unsafeCoerce' that only works for converting to/from 'Any'. Still just as
-- -- unsafe, but makes it slightly more difficult to accidentally misuse.
-- pattern Any :: forall a. a -> Any
-- pattern Any a <- (unsafeCoerce -> a)
--   where Any = unsafeCoerce
-- {-# COMPLETE Any #-}
--
-- -- | Used to explicitly overwrite references to values that should not be retained by the GC.
-- null# :: Any
-- null# = Any ()
--
-- newEmptyFrames :: IO (Frames '[])
-- newEmptyFrames = Frames 0 <$> newSmallArray 32 null#
--
-- withDepthOf :: forall fs r. Frames fs -> (Depth fs => r) -> r
-- withDepthOf (Frames len _) = reflectDict @(Depth fs) len
--
-- -- peekFrame :: Frames (f fs) -> ST (S fs) (Frame f fs)
-- -- peekFrame (Frames len fs) = readSmallArray fs (len - 1) <&> \(Any f) -> f
--
-- lookupFrame
--   :: forall f fs2 r. (DebugCallStack, f :<# fs2)
--   => Frames fs2
--   -> (forall fs1. (f ': fs1) :<<# fs2 => Proxy# fs1 -> Frame f fs1 -> IO r)
--   -> IO r
-- lookupFrame (Frames len fs) k = do
--   { let idx = reifyIndexF @f @fs2
--   ; assertM $ idx < len
--   ; Any f <- readSmallArray fs idx
--   ; reflectDict @((f ': fs1) :<<# fs2) idx
--   $ k @fs1 proxy# f
--   } :: forall (fs1 :: [FrameK]). IO r
--
-- -- | Looks up a 'Frame' given a 'Target' into a stack of 'Frames'. The result is returned by passing
-- -- it to the given continuation so that the @f@ and @fs2@ variables can be bound existentially.
-- indexFrame
--   :: forall eff fs1 r. DebugCallStack => Target eff fs1 -> Frames fs1
--   -> (forall f fs2. (eff ~ FrameEffect f, (f ': fs2) :<<# fs1)
--       => Proxy# (f ': fs2) -> Frame f fs2 -> IO r)
--   -> IO r
-- indexFrame (Target idx) (Frames len fs) k = do
--   { assertM $ idx < len
--   ; with (axiom @eff @(FrameEffect f)) do
--   { Any f <- readSmallArray fs idx
--   ; reflectDict @((f ': fs2) :<<# fs1) idx
--   $ k @f @fs2 proxy# f
--   }} :: forall (f :: FrameK) (fs2 :: [FrameK]). IO r
--
-- pushFrame :: DebugCallStack => Frame f fs -> Frames fs -> IO (Frames (f ': fs))
-- pushFrame f (Frames len fs1) = do
--   fs2 <- if
--     | len == sizeofSmallMutableArray fs1 -> do
--         -- out of space, resize and copy
--         fs2 <- newSmallArray (len * 2) null#
--         copySmallMutableArray fs2 0 fs1 0 len
--         pure fs2
--     | otherwise -> do
--         -- no need to resize, reuse the input array
--         assertM $ len >= 0
--         assertM $ len < sizeofSmallMutableArray fs1
--         pure fs1
--   assertM $ len + 1 <= sizeofSmallMutableArray fs2
--   writeSmallArray fs2 len (Any f)
--   pure $! Frames (len + 1) fs2
--
-- popFrame :: DebugCallStack => Frames (f ': fs) -> IO (Frame f fs, Frames fs)
-- popFrame (Frames len fs) = do
--   -- Note that we never resize the frames stack when popping, only when pushing, so the size of the
--   -- frames stack will never decrease. Theoretically, if someone created a giant frames stack very
--   -- briefly, then executed a long-lived computation with a much smaller stack, this would leak
--   -- memory. However, such a usage pattern seems unlikely, so for now, we never decrease the size of
--   -- the stack.
--   Any f <- readSmallArray fs (len - 1)
--   writeSmallArray fs len null#
--   pure (f, Frames (len - 1) fs)
--
-- -- dropFrames :: forall fs1 fs2. (DebugCallStack, fs1 :<<# fs2) => Frames fs2 -> ST (S fs2) (Frames fs1)
-- -- dropFrames (Frames len1 fs) = with (rootsEq @fs1 @fs2) do
-- --   let len2 = reifySubIndexF @fs1 @fs2
-- --   assertM $ len2 <= len1
-- --   for_ [len2..len1-1] \idx ->
-- --     writeSmallArray fs idx null#
-- --   pure $ Frames len2 fs

-- -- -------------------------------------------------------------------------------------------------
-- -- targets
--
-- newTarget :: forall f fs. f :<# fs => Target (FrameEffect f) fs
-- newTarget = Target $ reifyIndexF @f @fs
--
-- noTargets :: Targets '[] fs
-- noTargets = Targets mempty
--
-- weakenTargets :: fs1 :<<# fs2 => Targets effs fs1 -> Targets effs fs2
-- weakenTargets (Targets ts) = Targets ts
--
-- lookupTarget :: forall eff effs fs. (DebugCallStack, eff :< effs) => Targets effs fs -> Target eff fs
-- lookupTarget (Targets ts) = Target $ indexPrimArray ts (reifyIndex @eff @effs)
--
-- pushTarget :: Target eff fs -> Targets effs fs -> Targets (eff ': effs) fs
-- pushTarget (Target t) (Targets ts1) = Targets $ runPrimArray do
--   let len = sizeofPrimArray ts1
--   ts2 <- newPrimArray (len + 1)
--   writePrimArray ts2 0 t
--   copyPrimArray ts2 1 ts1 0 len
--   pure ts2
--
-- -- | A convenience operation for the common case of pushing a new target that maps an effect to a
-- -- newly-introduced frame.
-- pushNewTarget :: forall f effs fs. Depth fs => Targets effs fs -> Targets (FrameEffect f ': effs) (f ': fs)
-- pushNewTarget = pushTarget (newTarget @f) . weakenTargets
--
-- dropTargets
--   :: forall effs1 effs2 fs. (DebugCallStack, effs1 :<< effs2)
--   => Targets effs2 fs -> Targets effs1 fs
-- dropTargets (Targets ts) =
--   let idx = reifySubIndex @effs1 @effs2
--       len = sizeofPrimArray ts - idx
--   in Targets $ clonePrimArray ts idx len

-- -------------------------------------------------------------------------------------------------
-- core Eff operations

instance Functor (Eff effs) where
  fmap f m = m >>= pure . f
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff \_ _ -> pure a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff m >>= f = Eff \pid ts -> m pid ts >>= \a -> unEff (f a) pid ts
  {-# INLINE (>>=) #-}

-- run :: Eff '[] a -> a
-- run (Eff m) = unsafeDupablePerformIO do
--   fs <- newEmptyFrames
--   (_, a) <- m $! Context noTargets EmptyTargetsStack fs
--   pure a
--
-- lift :: effs1 :<< effs2 => Eff effs1 ~> Eff effs2
-- lift (Eff m) = Eff \(Context ts1 tss1 fs1) -> do
--   let !ctx1 = Context (dropTargets ts1) (PushTargets ts1 tss1) fs1
--   (Context _ (PushTargets ts2 tss2) fs2, a) <- m ctx1
--   let !ctx2 = Context ts2 tss2 fs2
--   pure (ctx2, a)
--
-- -- | Like 'lift', but restricted to introducing a single additional effect in the result. This is
-- -- behaviorally identical to just using 'lift', but the restricted type can produce better type
-- -- inference.
-- lift1 :: forall eff effs. Eff effs ~> Eff (eff ': effs)
-- lift1 = lift
-- {-# INLINE lift1 #-}

-- -------------------------------------------------------------------------------------------------
-- Handling

type Handling :: Effect -> [Effect] -> Type -> [Effect] -> Constraint
class Handling eff effs i effs' | eff effs' -> i effs where
  reifyHandlerIndex :: Int
type instance DictRep (Handling eff effs i effs') = Int

-- reflectHandling
--   :: forall eff effs1 effss i fs1 effs2 fs2 r. ('PROMPT eff effs1 i effss ': fs1) :<<# fs2
--   => Targets effs2 fs2
--   -- ^ A proof that this list of effects is fully handled by the current stack of frames.
--   -> (Handling eff effs1 i effs2 => r) -> r
-- reflectHandling !_ =
--   reflectDict @(Handling eff effs1 i effs2) $ reifySubIndexF @('PROMPT eff effs1 i effss ': fs1) @fs2
--
-- withHandling
--   :: forall eff effs' fs effs i r. Handling eff effs i effs'
--   => Targets effs' fs
--   -- ^ A proof that we’re in a context where the 'Handling' constraint actually applies.
--   -> (forall effss. 'PROMPT eff effs i effss :<# fs => Proxy# effss -> r)
--   -> r
-- withHandling !_ k =
--   ( reflectDict @('PROMPT eff effs i effss :<# fs) (reifyHandlerIndex @eff @effs @i @effs')
--   $ k @effss proxy#
--   ) :: forall (effss :: [[Effect]]). r

type Handling# :: Effect -> [Effect] -> Type -> [Effect] -> TYPE 'IntRep
newtype Handling# eff effs i effs' = Handling# { handlerIndex# :: Int# }
-- TODO: Replace with Dict# abstraction?

-- reifyHandling# :: forall eff effs i effs'. Handling eff effs i effs' => Handling# eff effs i effs'
-- reifyHandling# = let !(I# n) = reifyHandlerIndex @eff @effs @i @effs' in Handling# n
--
-- reflectHandling#
--   :: forall eff effs i effs' r. Handling# eff effs i effs' -> (Handling eff effs i effs' => r) -> r
-- reflectHandling# (Handling# n) = reflectDict @(Handling eff effs i effs') (I# n)

-- -- | See 'LiftH'.
-- type RelativeHandling :: Effect -> [Effect] -> Type -> [Effect] -> Type
-- newtype RelativeHandling eff effs i effs' = RelativeHandling Int
--
-- reifyRelativeHandling
--   :: forall eff effs2 effs1 i fs. Handling eff effs1 i effs2
--   => effs2 :->> fs -> Frames fs -> RelativeHandling eff effs1 i effs2
-- reifyRelativeHandling !_ (Frames len _) =
--   RelativeHandling (len - reifyHandlerIndex @eff @effs1 @i @effs2)
--
-- reflectRelativeHandling
--   :: forall eff effs2 effs1 i fs r
--    . effs2 :->> fs -> Frames fs -> RelativeHandling eff effs1 i effs2
--   -> (Handling eff effs1 i effs2 => r) -> r
-- reflectRelativeHandling !_ (Frames len _) (RelativeHandling idx) =
--   reflectDict @(Handling eff effs1 i effs2) (len - idx)

-- -------------------------------------------------------------------------------------------------
-- Eff operations that use Handling

-- send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
-- send e = Eff \ctx@(Context ts _ fs) ->
--   with (handles e) $
--   indexFrame (lookupTarget @eff ts) fs \(_ :: Proxy# (f ': fs)) p ->
--   withHandlesImpliesPrompt @f \(_ :: Proxy# ('PROMPT eff effs2 i effss)) ->
--   reflectHandling @eff @effs2 @effss @i @fs ts $
--     unEff (pHandler p reifyHandling# e) ctx
--
-- handle
--   :: forall eff a effs. Handles eff
--   => (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
--   -> Eff (eff ': effs) a
--   -> Eff effs a
-- handle f (Eff m) = Eff \(Context ts1 tss1 (fs1 :: Frames fs1) :: Context effs effss1) ->
--   withDepthOf fs1 do
--     let ts2 :: Targets (eff ': effs) ('PROMPT eff effs a effss1 ': fs1)
--         ts2 = pushNewTarget ts1
--
--         f1 :: Frame ('PROMPT eff effs a effss1) fs1
--         f1 = Prompt
--           { pHandler = \n e -> reflectHandling# n $ f e
--           , pTargets = ts2
--           , pTargetsStack = PushTargets ts1 tss1
--           }
--
--     fs2 <- pushFrame f1 fs1
--     let !ctx1 = Context ts2 EmptyTargetsStack fs2
--     (Context _ _ (ffs3 :: Frames fs2), a) <- m ctx1
--     with (axiom @('PROMPT eff effs a effss1 ': fs1) @fs2) do -- FIXME: bogus!!!
--       (f3, fs3) <- popFrame ffs3
--       let PushTargets ts3 tss3 = pTargetsStack f3
--           !ctx2 = Context ts3 tss3 fs3
--       pure (ctx2, a)
--
-- liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
-- liftH (Eff m) = Eff \(Context ts1 tss1 fs1) ->
--   withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
--   lookupFrame @('PROMPT eff effs i effss) fs1 \_ p -> do
--     let !ctx1 = Context (weakenTargets $ pTargets p) (PushTargets ts1 tss1) fs1
--     (Context _ (PushTargets ts2 tss2) fs2, a) <- m ctx1
--     let !ctx2 = Context ts2 tss2 fs2
--     pure (ctx2, a)

-- abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
-- abort a = Eff \_ (Context ts1 _ _ (fs1 :: Frames fs1)) ->
--   withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
--   lookupFrame @('PROMPT eff effs i effss) fs1 \(_ :: Proxy# fs2) p ->
--   withWeakenSubIndex @('PROMPT eff effs i effss) @fs2 @fs1 $
--   with (rootsEq @fs2 @fs1) do
--     let !(PushTargets ts2 tss2) = pTargetss p
--         !trs2 = pRemappings p
--     fs2 <- dropFrames fs1
--     pCont p topsRefl a (Context ts2 tss2 trs2 fs2)

-- -------------------------------------------------------------------------------------------------



{-

-- -------------------------------------------------------------------------------------------------

type family xs ++ ys where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

-- -------------------------------------------------------------------------------------------------

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

-- | The list of effects made “visible” by the current stack of frames without any uses of 'liftH'
-- or related operations.
type VisibleEffects :: FramesK -> [Effect]
type family VisibleEffects fs where
  VisibleEffects ('ROOT _ _) = '[]
  VisibleEffects ('CELL s fs) = Cell s ': VisibleEffects fs
  VisibleEffects ('PROMPT eff effs _ _ _) = eff ': effs

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
  :: forall fs1 fs2. () => forall eff effs i effss1 fs3 effss2 fs4
   . (fs1 ~ 'PROMPT eff effs i effss1 fs3, fs2 ~ 'PROMPT eff effs i effss2 fs4) => fs1 ^~ fs2
pattern Prompts <-
  ((\_ -> (# unsafeRefl# void#, unsafeRefl# void# #)
       :: forall eff effs i effss1 fs3 effss2 fs4
        . (# fs1 ~# 'PROMPT eff effs i effss1 fs3, fs2 ~# 'PROMPT eff effs i effss2 fs4 #))
  -> (# Refl#, Refl# #))
  where Prompts = UnsafeTopsEq void#

topsRefl :: fs1 ~ fs2 => fs1 ^~ fs2
topsRefl = UnsafeTopsEq void#
{-# INLINE topsRefl #-}

topsSym :: fs1 ^~ fs2 -> fs2 ^~ fs1
topsSym _ = UnsafeTopsEq void#
{-# INLINE topsSym #-}

topsTrans :: fs1 ^~ fs2 -> fs2 ^~ fs3 -> fs1 ^~ fs3
topsTrans _ _ = UnsafeTopsEq void#
{-# INLINE topsTrans #-}

-- -------------------------------------------------------------------------------------------------

newtype Eff effs a = Eff
  { unEff :: forall fs
           . (effs ': effss) :~>> VisibleEffects fs
          -> Context effs effss fs
          -> ST (S fs) (Context effs effss)
            forall effss fs1
           . (forall fs2. fs1 ^~ fs2 -> a -> Context effs effss fs2 -> ST (S fs2) (R fs2))
          -> Context effs effss fs1 -> ST (S fs1) (R fs1)
  }

-- | Note: we store @effs ':->>' fs@ separately from @effss ':=>>' fs@ (rather than simply storing
-- a single value of type @(effs ': effss) ':=>>' fs@) to avoid a pointer indirection when
-- retrieving the topmost targets. It isn’t clear if this is beneficial in general, as it requires
-- an additional argument to be passed on the stack; benchmarking the difference would be useful.
data Context effs effss fs
  = Context {-# UNPACK #-} (effs :->> fs) (effss :=>> fs) {-# UNPACK #-} (Frames fs)

-- | A stack of metacontinuation frames. The 'Int' field contains the logical size of the current
-- frames stack; the 'SmallMutableArray' is usually a little larger than the logical size so we
-- don’t have to do so much copying. When the stack overflows, we allocate a new, larger stack and
-- copy the old frames into the new stack (and the old stack can be deallocated by the GC).
data Frames fs = Frames {-# UNPACK #-} Int {-# UNPACK #-} (SmallMutableArray (S fs) Any)

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
    , pRemappings :: (effs ': effss) :~>> VisibleEffects fs
    } -> Frame ('PROMPT eff effs i effss) fs

-- -------------------------------------------------------------------------------------------------

{- The arrow zoo:

  * eff   :->  fs    — target indirection index
  * effs  :->> fs    — target indirection vector
  * effss :=>> fs    — target indirection stack
  * effs  :~>> effss — target remapping stack

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
type (:~>>) :: [[Effect]] -> [Effect] -> Type
data effss :~>> effs where
  Run :: '[effs] :~>> effs
  Lift :: effs1 :<<: effs2
       -> (effs2 ': effss) :~>> effs3
       -> (effs1 ': effs2 ': effss) :~>> effs3
  LiftH :: {-# UNPACK #-} RelativeHandling eff effs i effs2
        -- ^ The index of the prompt frame we’re lifting to, stored as a relative offset /backwards/
        -- from the current topmost frame. Why do we store it this way? Well, if we stored it as an
        -- absolute index, the index might have to be shifted on continuation restore, since the
        -- length of the new frames stack might be different.
        --
        -- Storing the index this way is entirely safe, as the frame being lifted to is guaranteed
        -- to be in the captured part of the frames stack. If it wasn’t, we’d be in big trouble, as
        -- we wouldn’t have a frame to lift to! Fortunately, this property holds: once you call
        -- 'liftH', you can’t capture a more-nested continuation anymore because the only way to get
        -- back into a more-nested context is to return from the call to 'liftH'.
        --
        -- (Technically, you can capture a more-nested continuation by installing a totally new
        -- prompt and capturing up to that, but that’s a new prompt, so it won’t have the 'LiftH'
        -- remapping frame in it, anyway.)
        --
        -- It would be nice to encode this subtlety in the type system somehow, but I’m not sure how
        -- to do it.
        -> (effs2 ': effss) :~>> effs3
        -> ((eff ': effs) ': effs2 ': effss) :~>> effs3

-- -------------------------------------------------------------------------------------------------
-- remappings

popRemapping :: (effs1 ': effs2 ': effss) :~>> effs3 -> (effs2 ': effss) :~>> effs3
popRemapping (Lift _ trs) = trs
popRemapping (LiftH _ trs) = trs

replayRemappings
  :: forall effss effs fs
   . effss :~>> effs
  -> effs :->> fs
  -> Frames fs
  -> ST (S fs) (effss :=>> fs)
  -- ^ Note: this runs in 'ST', but it doesn’t mutate any state, it only needs read-ordering
  -- guarantees.
replayRemappings Run ts _ = pure $! PushTargets ts NoTargetss
replayRemappings (Lift idx trs) ts fs = do
  tss <- replayRemappings trs ts fs
  reflectSubIndex# idx $
    pure $! PushTargets (dropTargets $ peekTargets tss) tss
replayRemappings (LiftH (idx :: RelativeHandling eff effs2 i effs3) trs) ts1 fs = do
  tss <- replayRemappings trs ts1 fs
  let ts2 = peekTargets tss
  reflectRelativeHandling ts2 fs idx $
    withHandling @eff @effs3 ts2 \(_ :: Proxy# effss2) ->
    lookupFrame @('PROMPT eff effs2 i effss2) fs \_ p ->
      pure $! PushTargets (weakenTargets $ pTargets p) tss

-- -------------------------------------------------------------------------------------------------
-- continuations

type Continuation :: Type -> [FrameK] -> Effect -> [Effect] -> Type -> Type
data Continuation a fs eff effs i = Continuation
  { cRootHandler :: forall effs'. Handling# eff effs i effs' -> eff (Eff effs') ~> Eff effs'
  -- ^ The handler function of the handler this continuation captures up to. This is stored
  -- separately from the 'cCapturedFrames' array because the continuation and remappings of the
  -- resulting prompt are provided by the context in which the continuation is restored, so only
  -- storing the handler is necessary.
  , cCapturedFrames :: {-# UNPACK #-} SmallArray Any
  -- ^ An array of 'CapturedFrame's, one per element of @fs@.
  , cCont :: forall effss fs1 fs2. fs2 ~ RestoreFrames fs ('PROMPT eff effs i effss fs1)
          => Proxy# effss -> Proxy# fs1 -> a -> VisibleEffects fs2 :->> fs2 -> Frames fs2
          -> ST (S fs2) (R fs2)
  -- ^ The portion of the captured continuation that is not contained within any metacontinuation
  -- frames.
  }

type CapturedFrame :: FrameK -> FramesK -> Type
data CapturedFrame f fs where
  CCell :: ~s -> CapturedFrame ('CELL s) fs
  CPrompt ::
    { cpCont :: forall fs2. fs ^~ fs2 -> i -> Context effs effss fs2 -> ST (S fs2) (R fs2)
    , cpHandler :: forall effs'. Handling# eff effs i effs' -> eff (Eff effs') ~> Eff effs'
    , cpRemappings :: (effs ': effss) :~>> VisibleEffects fs
    } -> CapturedFrame ('PROMPT eff effs i effss) fs

type RestoreFrames :: [FrameK] -> FramesK -> FramesK
type family RestoreFrames fs1 fs2 where
  RestoreFrames '[]        fs  = fs
  RestoreFrames (f ': fs1) fs2 = f (RestoreFrames fs1 fs2)

restorePreservesVisibleEffectsEq
  :: forall cfs fs1 fs2. VisibleEffects fs1 ~ VisibleEffects fs2
  => VisibleEffects (RestoreFrames cfs fs1) :~: VisibleEffects (RestoreFrames cfs fs2)
restorePreservesVisibleEffectsEq = axiom
{-# INLINE restorePreservesVisibleEffectsEq #-}

restorePreservesTopsEq
  :: forall cfs fs1 fs2. fs1 ^~ fs2
  -> RestoreFrames cfs fs1 ^~ RestoreFrames cfs fs2
restorePreservesTopsEq _ = UnsafeTopsEq void#
{-# INLINE restorePreservesTopsEq #-}

captureContinuation
  :: forall eff effs1 i effss1 fs1 a effs2 effss2 fs2 r
   . 'PROMPT eff effs1 i effss1 fs1 :<<# fs2
  => (forall fs3. fs2 ^~ fs3 -> a -> Context effs2 effss2 fs3 -> ST (S fs3) (R fs3))
  -> (effs2 ': effss2) :~>> VisibleEffects fs2
  -> Frames fs2
  -> (forall cfs. fs2 ~ RestoreFrames cfs ('PROMPT eff effs1 i effss1 fs1)
      => Continuation a cfs eff effs1 i -> ST (S fs2) r)
  -> ST (S fs2) r
captureContinuation k1 trs (Frames len_fs fs1) k2 = do
  let idx_fs = reifySubIndexF @('PROMPT eff effs1 i effss1 fs1) @fs2
  assertM $ idx_fs < len_fs
  Any (f :: Frame ('PROMPT eff effs1 i effss1) fs1) <- readSmallArray fs1 idx_fs
  cfs <- captureFrames idx_fs
  ( with (axiom @fs2 @(RestoreFrames cfs ('PROMPT eff effs1 i effss1 fs1)))
    $ k2 @cfs $! Continuation (pHandler f) cfs (k3 @cfs)
    ) :: forall (cfs :: [FrameK]). ST (S fs2) r
  where
    captureFrames idx_fs = unsafeFreezeSmallArray =<< do
      let len_cfs = len_fs - (idx_fs + 1)
      cfs <- newSmallArray len_cfs null#
      for_ [0..len_cfs-1] \idx_cfs -> do
        Any f <- readSmallArray fs1 (idx_fs + 1 + idx_cfs)
        let !cf = captureFrame f
        writeSmallArray cfs idx_cfs (Any cf)
      pure cfs

    k3 :: forall cfs effss3 fs3 fs4 pfs1 pfs3
        . ( pfs1 ~ 'PROMPT eff effs1 i effss1 fs1
          , pfs3 ~ 'PROMPT eff effs1 i effss3 fs3
          , fs2 ~ RestoreFrames cfs pfs1
          , fs4 ~ RestoreFrames cfs pfs3 )
       => Proxy# effss3 -> Proxy# fs3
       -> a -> VisibleEffects fs4 :->> fs4 -> Frames fs4
       -> ST (S fs4) (R fs4)
    k3 _ _ a ts1 fs2 =
      with (restorePreservesVisibleEffectsEq @cfs @pfs3 @pfs1) do
        let tops = restorePreservesTopsEq @cfs @pfs3 @pfs1 Prompts
        PushTargets ts2 tss2 <- replayRemappings trs ts1 fs2
        k1 (topsSym tops) a (Context ts2 tss2 trs fs2)

restoreContinuation
  :: forall a cfs eff effs i effss fs1
   . Continuation a cfs eff effs i
  -> (forall fs2. fs1 ^~ fs2 -> i -> Context effs effss fs2 -> ST (S fs2) (R fs2))
  -> a -> Context effs effss fs1 -> ST (S fs1) (R fs1)
restoreContinuation (Continuation h cfs k1) k2 a (Context ts1 tss trs fs1) =
  withDepthOf fs1 do
    let ts2 = pushNewTarget ts1
        f = Prompt k2 h ts2 (PushTargets ts1 tss) trs
    fs2 <- pushFrame f fs1
    restoreFrames 0 ts2 fs2
  where
    restoreFrames
      :: forall fs2
       . Int
      -> VisibleEffects fs2 :->> fs2
      -> Frames fs2
      -> ST (S fs2) (R fs2)
    restoreFrames idx ts2 fs2
      | idx < sizeofSmallArray cfs = do
          let !(# Any cf #) = indexSmallArray cfs idx
          (ts3, fs3) <- restoreFrame cf ts2 fs2
          restoreFrames (idx + 1) ts3 fs3
      | otherwise =
          with (axiom @fs2 @(RestoreFrames cfs ('PROMPT eff effs i effss fs1))) $
            k1 @effss @fs1 proxy# proxy# a ts2 fs2

captureFrame :: Frame f fs -> CapturedFrame f fs
captureFrame Prompt { pCont = k, pHandler = h, pRemappings = trs } = CPrompt k h trs
captureFrame (Cell s) = CCell s

restoreFrame
  :: forall f fs
   . CapturedFrame f fs
  -> VisibleEffects fs :->> fs
  -> Frames fs
  -> ST (S fs) (VisibleEffects (f fs) :->> f fs, Frames (f fs))
restoreFrame (CCell s) ts fs1 =
  letT @f \(_ :: Proxy# ('CELL s)) ->
  withDepthOf fs1 do
    fs2 <- pushFrame (Cell s) fs1
    pure (pushNewTarget ts, fs2)
restoreFrame (CPrompt k2 h trs) ts1 fs1 =
  letT @f \(_ :: Proxy# ('PROMPT eff effs i effss2)) ->
  withDepthOf fs1 do
    tss <- replayRemappings trs ts1 fs1
    let ts2 = pushNewTarget $ peekTargets tss
    fs2 <- pushFrame (Prompt k2 h ts2 tss trs) fs1
    pure (ts2, fs2)

shift
  :: forall eff effs i effs' a. Handling eff effs i effs'
  => ((a -> Eff effs i) -> Eff effs i) -> Eff effs' a
shift f = Eff \k1 (Context ts1 _ trs1 (fs1 :: Frames fs1)) ->
  withHandling @eff @effs' ts1 \(_ :: Proxy# effss) ->
  lookupFrame @('PROMPT eff effs i effss) fs1 \(_ :: Proxy# fs2) p ->
  captureContinuation @eff @effs @i @effss @fs2 k1 trs1 fs1 \cont ->
  withWeakenSubIndex @('PROMPT eff effs i effss) @fs2 @fs1 $
  with (rootsEq @fs2 @fs1) do
    let m :: Eff effs i
        m = f \a -> Eff \k2 ctx -> restoreContinuation cont k2 a ctx
        !(PushTargets ts2 tss2) = pTargetss p
        !trs2 = pRemappings p
    fs2 <- dropFrames fs1
    unEff m (pCont p) (Context ts2 tss2 trs2 fs2)

-- -------------------------------------------------------------------------------------------------

-}
