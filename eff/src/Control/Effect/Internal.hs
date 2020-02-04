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
import GHC.Exts (Any, Int(..), Int#, Proxy#, RealWorld, RuntimeRep(..), SmallArray#, State#, TYPE, Void#, (+#), proxy#, runRW#, void#)
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
reflectDict !d x = unsafeCoerce (WithDict @c @r x) d
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

type instance DictRep (eff :< effs) = Int
type instance DictRep (effs1 :<< effs2) = Int

-- -------------------------------------------------------------------------------------------------

type Effect = (Type -> Type) -> Type -> Type

-- -------------------------------------------------------------------------------------------------

type Eff :: [Effect] -> Type -> Type
newtype Eff effs a = Eff# { unEff# :: PromptId -> SmallArray# Any -> IO a }

pattern Eff :: (PromptId -> Targets effs -> IO a) -> Eff effs a
pattern Eff { unEff } <- Eff# ((\f pid (Targets (SmallArray ts)) -> f pid ts) -> unEff)
  where Eff f = Eff# \pid ts -> f pid (Targets (SmallArray ts))
{-# COMPLETE Eff #-}

newtype Handler eff = Handler { runHandler :: forall effs. eff (Eff effs) ~> Eff effs }

type Targets :: [Effect] -> Type
type role Targets nominal
newtype Targets effs = Targets (SmallArray Any)

data AbortException = AbortException PromptId ~Any
instance Show AbortException where
  show (AbortException _ _) = "AbortException"
instance Exception AbortException

newtype PromptId = PromptId# Int#
pattern PromptId :: Int -> PromptId
pattern PromptId{ unPromptId } <- PromptId# (I# -> unPromptId)
  where PromptId (I# n) = PromptId# n
{-# COMPLETE PromptId #-}

newtype Winder effs1 effs2 a b = Winder
  { winder :: PromptId -> Targets effs1 -> IO (Targets effs2, Unwinder effs1 effs2 a b) }

data Unwinder effs1 effs2 a b = Unwinder
  { returnUnwinder :: a -> IO b
  , abortUnwinder :: IO ()
  -- ^ Called when this prompt is unwound due to an abort to an /enclosing/ prompt. The prompt that
  -- is aborted to has its 'returnUnwinder' handler called, __/not/__ its 'abortUnwinder' handler!
  , captureUnwinder :: IO (Winder effs1 effs2 a b) }

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
--
-- TODO: Ensure the recursive definition of rewind doesn’t defeat important optimizations.
-- Specifically, it’s worth ensuring that simple handlers never actually allocate any Unwinder
-- closures at all and the recursive call to wind is just a jump to a known function.
wind :: forall effs1 effs2 a b. Winder effs1 effs2 a b -> Eff effs2 a -> Eff effs1 b
wind winder = rewind winder . fmap Return

rewind :: forall effs1 effs2 a b. Winder effs1 effs2 a b -> Eff effs2 (Request effs2 a) -> Eff effs1 b
rewind Winder{ winder } (Eff m) = Eff \pid1 ts1 -> do
  -- Start by applying the winder.
  let pid2 = PromptId (unPromptId pid1 + 1)
  (ts2, Unwinder{ returnUnwinder, abortUnwinder, captureUnwinder }) <- winder pid2 ts1
  -- Push a new prompt frame and invoke the delimited computation.
  request <- IO.reset (m pid2 ts2) `IO.catch` \exn@(AbortException target (Any a)) ->
    if unPromptId target == unPromptId pid2
      -- The computation was aborted to this prompt; treat it like a normal return.
      then pure $! Return a
      -- The computation was aborted to an enclosing prompt; call the abort unwinder and re-raise
      -- the exception.
      else abortUnwinder *> IO.throwIO exn
  case request of
    -- Normal return; call the unwinder and return the result.
    Return a -> returnUnwinder a
    -- Someone called shift, so we’re capturing the continuation.
    Capture target k1 (f :: (c -> Eff effs3 d) -> Eff effs3 d) -> do
      -- Start by calling the capture unwinder.
      rewinder <- captureUnwinder
      -- Compose the continuation with the rewinder.
      let !k2 = rewind rewinder . k1
      if unPromptId target == unPromptId pid2
        -- We’re capturing up to this prompt, so we’re done unwinding; invoke the
        -- metacontinuation.
        then with (axiom @effs1 @effs3) $ with (axiom @b @d) $ unEff (f k2) pid1 ts1
        -- We’re capturing up to a parent prompt, so capture the next continuation slice.
        else IO.shift \k# -> do
          -- Extend the continuation up to this prompt by composing it with the continuation up to
          -- the next prompt.
          let k3 b = Eff \pid3 ts3 -> IO.applyContinuation k# $ unEff (k2 b) pid3 ts3
          pure $! Capture target k3 f


-- -------------------------------------------------------------------------------------------------
-- targets

-- | A restricted form of 'unsafeCoerce' that only works for converting to/from 'Any'. Still just as
-- unsafe, but makes it slightly more difficult to accidentally misuse.
pattern Any :: forall a. a -> Any
pattern Any a <- (unsafeCoerce -> a)
  where Any = unsafeCoerce
{-# COMPLETE Any #-}

-- | Used to explicitly overwrite references to values that should not be retained by the GC.
null# :: Any
null# = Any ()

noTargets :: Targets '[]
noTargets = Targets mempty

lookupTarget :: forall eff effs. (DebugCallStack, eff :< effs) => Targets effs -> Handler eff
lookupTarget (Targets ts) = case indexSmallArray ts (reifyIndex @eff @effs) of (# Any h #) -> h

pushTarget :: Handler eff -> Targets effs -> Targets (eff ': effs)
pushTarget !h (Targets ts1) = Targets $ runSmallArray do
  let len = sizeofSmallArray ts1
  ts2 <- newSmallArray (len + 1) null#
  writeSmallArray ts2 0 (Any h)
  copySmallArray ts2 1 ts1 0 len
  pure ts2

dropTargets
  :: forall effs1 effs2. (DebugCallStack, effs1 :<< effs2)
  => Targets effs2 -> Targets effs1
dropTargets (Targets ts) =
  let idx = reifySubIndex @effs1 @effs2
      len = sizeofSmallArray ts - idx
  in Targets $ cloneSmallArray ts idx len

-- -------------------------------------------------------------------------------------------------
-- core Eff operations

instance Functor (Eff effs) where
  fmap f m = m >>= pure . f
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff# \_ _ -> pure a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff# m >>= f = Eff# \pid ts -> m pid ts >>= \a -> unEff# (f a) pid ts
  {-# INLINE (>>=) #-}

run :: Eff '[] a -> a
run (Eff m) = unsafeDupablePerformIO $ m (PromptId 0) noTargets

lift :: effs1 :<< effs2 => Eff effs1 ~> Eff effs2
lift (Eff m) = Eff \pid ts -> m pid (dropTargets ts)

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
  reifyHandlerContext :: HandlerContext eff effs
type instance DictRep (Handling eff effs _ _) = HandlerContext eff effs

type HandlerContext :: Effect -> [Effect] -> Type
data HandlerContext eff effs
  -- The Targets field needs to be lazy, as it involves a small bit of knot-tying: the Handler
  -- closure stored in the Targets references the HandlerContext, and the simplest place to break
  -- the cycle is here.
  = HandlerContext PromptId ~(Targets (eff ': effs))

-- -------------------------------------------------------------------------------------------------
-- Eff operations that use Handling

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \pid ts -> unEff (runHandler (lookupTarget ts) e) pid ts

handle
  :: forall eff a effs
   . (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f = wind winder where
  winder = Winder \pid ts1 -> do
    let h :: forall effs'. eff (Eff effs') ~> Eff effs'
        h = reflectDict @(Handling eff effs a effs') (HandlerContext pid ts2) f
        ts2 = pushTarget (Handler h) ts1
    pure (ts2, unwinder)
  unwinder = Unwinder pure (pure ()) (pure winder)

liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff m) = Eff \pid _ -> do
  let !(HandlerContext _ ts) = reifyHandlerContext @eff @effs @i @effs'
  m pid ts

abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
abort a = Eff \_ _ -> do
  let !(HandlerContext target _) = reifyHandlerContext @eff @effs @i @effs'
  IO.throwIO $! AbortException target (Any a)

shift
  :: forall eff effs i effs' a. Handling eff effs i effs'
  => ((a -> Eff effs i) -> Eff effs i) -> Eff effs' a
shift f = Eff \_ _ -> do
  let !(HandlerContext target _) = reifyHandlerContext @eff @effs @i @effs'
  IO.shift \k# -> do
    let k a = Eff \_ _ -> IO.applyContinuation k# (pure a)
    pure $! Capture target k f

-- -------------------------------------------------------------------------------------------------
-- Eff operations that use Handling

class Swizzle effs1 effs2 where
  swizzleTargets :: Targets effs2 -> Targets effs1
instance {-# INCOHERENT #-} effs1 :<< effs2 => Swizzle effs1 effs2 where
  swizzleTargets = dropTargets
  {-# INLINE swizzleTargets #-}
instance Swizzle '[] effs where
  swizzleTargets _ = noTargets
  {-# INLINE swizzleTargets #-}
instance (eff :< effs2, Swizzle effs1 effs2) => Swizzle (eff ': effs1) effs2 where
  swizzleTargets ts = pushTarget (lookupTarget @eff ts) $! swizzleTargets @effs1 ts

-- | A magician hands you a deck of cards.
--
-- “Take some cards off the top,” she tells you, “then put them back in any order you like.”
--
-- That’s what 'swizzle' does. If you picture the list of effects @effs@ like a deck of cards,
-- 'swizzle' allows you to rearrange it arbitrarily, so long as all the cards you started with are
-- still /somewhere/ in the deck when you’re finished. In fact, 'swizzle' is even more powerful than
-- that, as you may also add entirely new cards into the deck, as many as you please! You just can’t
-- take any cards out.
--
-- As it happens, the metaphor is apt for more reason than one, because 'swizzle' is slightly
-- magical. Under the hood, it tries its absolute best to figure out what you mean. Usually it does
-- a pretty good job, but sometimes it doesn’t get it quite right, and you may receive a rather
-- mystifying type error. In that case, fear not: all you need to do is offer it a little help by
-- adding some type annotations (or using @TypeApplications@).
swizzle :: forall effs1 effs2. Swizzle effs1 effs2 => Eff effs1 ~> Eff effs2
swizzle = wind winder where
  winder = Winder \_ ts -> pure (swizzleTargets @effs1 @effs2 ts, unwinder)
  unwinder = Unwinder pure (pure ()) (pure winder)
{-# INLINE swizzle #-}
