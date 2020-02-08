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

-- import qualified Control.Effect.Internal.Continuation as IO
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
import GHC.Exts (Any, Continuation#, Int(..), Int#, Proxy#, RealWorld, RuntimeRep(..), SmallArray#, State#, TYPE, Void#, (+#), proxy#, runRW#, void#, reset#, shift#, applyContinuation#)
import GHC.TypeLits (ErrorMessage(..), Nat, TypeError)
import GHC.Types (IO(..))
import Unsafe.Coerce (unsafeCoerce)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Data.Void
import Control.Monad.IO.Class
import Data.Primitive.Array
import Data.Function
import GHC.Magic (noinline)

import Control.Effect.Internal.Debug
import Control.Effect.Internal.Equality
import Control.Effect.Internal.PrimArray
import Control.Effect.Internal.SmallArray

import Debug.Trace

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

-- | A restricted form of 'unsafeCoerce' that only works for converting to/from 'Any'. Still just as
-- unsafe, but makes it slightly more difficult to accidentally misuse.
pattern Any :: forall a. a -> Any
pattern Any a <- (unsafeCoerce -> a)
  where Any = unsafeCoerce
{-# COMPLETE Any #-}

-- | Used to explicitly overwrite references to values that should not be retained by the GC.
null# :: Any
null# = Any ()

unIO :: IO a -> State# RealWorld -> (# State# RealWorld, a #)
unIO (IO m) = m
{-# INLINE unIO #-}

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

{- Note [The Eff Machine]
~~~~~~~~~~~~~~~~~~~~~~~~~
The Eff monad is best thought of as a “embedded virtual machine.” Given primitive support for
continuation manipulation from the host, Eff efficiently implements a complement of complex control
operations.

At any time, the Eff machine conceptually manages two pieces of state:

  1. The /metacontinuation stack/, which holds metacontinuation frames. Metacontinuation frames
     correspond to things like effect handlers, “thread-local” state, and dynamic winders.

  2. The /targets vector/, which maps a list of effects to the corresponding metacontinuation frames
     that handle them.

However, the representation of these things is somewhat contorted to optimize for the most common
cases. For example, many Eff computations never need to capture the continuation even once, so the
default representation of the metacontinuation stack optimizes for that scenario. If a continuation
is captured, the representation evolves as necessary to amortize the cost of further continuation
capture operations.

The state of the Eff machine is tracked by a set of virtual /registers/:

  * `targets` points to the current targets vector.

  * `underflow` points to a function that is called when the current continuation returns. This is
    initialized to simply return to the calling context that started the `Eff` computation in the
    first place, but continuation manipulation operations may change it.

  * `shift` points to a function that is called to capture the continuation up to a particular
     prompt.

  * `abort` points to a function that is called to abort to a particular prompt.

The functions pointed to by the `underflow`, `capture`, and `abort` registers modify the state of
the machine when they are called, so the registers interact in somewhat subtle ways. Applying a
captured continuation also modifies the state of the machine, but continuations may be applied in
an entirely different `Eff` computation than the one they were captured in, which requires delicate
care. -}

type Eff :: [Effect] -> Type -> Type
type role Eff nominal representational
newtype Eff effs a = Eff# { unEff# :: EVM a }
  deriving (Functor, Applicative, Monad)

pattern Eff :: (Registers -> IO (Registers, a)) -> Eff effs a
pattern Eff{unEff} = Eff# (EVM unEff)
{-# COMPLETE Eff #-}

type EVM :: TYPE r -> Type
newtype EVM a = EVM#
  { unEVM# :: Registers# -> State# RealWorld -> (# State# RealWorld, Registers#, a #) }

pattern EVM :: (Registers -> IO (Registers, a)) -> EVM a
pattern EVM{unEVM} <- EVM# ((\m (BoxRegisters rs1) -> IO \s1 -> case m rs1 s1 of (# s2, rs2, a #) -> (# s2, (BoxRegisters rs2, a) #)) -> unEVM)
  where EVM m = EVM# \rs1 s1 -> case m (BoxRegisters rs1) of IO f -> case f s1 of (# s2, (BoxRegisters rs2, a) #) -> (# s2, rs2, a #)
{-# COMPLETE EVM #-}

-- -------------------------------------------------------------------------------------------------

newtype Registers# = Registers# (# PromptId, Targets# #)

data Registers = BoxRegisters { unboxRegisters# :: Registers# }
pattern Registers :: PromptId -> Targets -> Registers
pattern Registers pid ts <- BoxRegisters (Registers# (# pid, (BoxTargets -> ts) #))
  where Registers pid (BoxTargets ts) = BoxRegisters (Registers# (# pid, ts #))
{-# COMPLETE Registers #-}

initialRegisters :: Registers
initialRegisters = Registers (PromptId 0) noTargets

newtype PromptId = PromptId# Int#
pattern PromptId :: Int -> PromptId
pattern PromptId{ unPromptId } <- PromptId# (I# -> unPromptId)
  where PromptId (I# n) = PromptId# n
{-# COMPLETE PromptId #-}

data AbortException = AbortException PromptId ~Any
instance Show AbortException where
  show (AbortException _ _) = "AbortException"
instance Exception AbortException

newtype Result# a = Result#
  (# (# Registers#, a #)
   | (# PromptId, Any, Any #)
   #)
pattern Return# :: Registers# -> a -> Result# a
pattern Return# rs a = Result# (# (# rs, a #) | #)
pattern Capture#
  :: PromptId
  -> ((b -> EVM c) -> EVM c)
  -> Continuation b a
  -> Result# a
pattern Capture# pid f k = Result# (# | (# pid, Any f, Any k #) #)
{-# COMPLETE Return#, Capture# #-}

data Result a = BoxResult (Result# a)
pattern Return :: Registers -> a -> Result a
pattern Return rs a <- BoxResult (Return# (BoxRegisters -> rs) a)
  where Return (BoxRegisters rs) a = BoxResult (Return# rs a)
pattern Capture
  :: PromptId
  -- ^ The prompt to capture up to.
  -> ((b -> EVM c) -> EVM c)
  -- ^ The metacontinuation passed by the user to the original call to 'shift'. This should be
  -- invoked with the fully-composed continuation after capturing is complete.
  -> Continuation b a
  -- ^ The composed continuation captured so far.
  -> Result a
pattern Capture pid f k = BoxResult (Capture# pid f k)
{-# COMPLETE Return, Capture #-}

newtype Continuation a b = Continuation#
  { runContinuation# :: a -> Registers# -> State# RealWorld -> (# State# RealWorld, Result# b #) }

pattern Continuation :: (a -> Registers -> IO (Result b)) -> Continuation a b
pattern Continuation{runContinuation} <- Continuation#
          ((\k a (BoxRegisters rs) -> IO \s1 ->
              case k a rs s1 of (# s2, r #) -> (# s2, BoxResult r #))
           -> runContinuation)
  where Continuation k = Continuation# \a rs s1 -> case unIO (k a (BoxRegisters rs)) s1 of
          (# s2, BoxResult r #) -> (# s2, r #)
{-# COMPLETE Continuation #-}

-- TODO: If all uses do `uncurry Return <$> m`, move it into this function.
resetVM :: IO (Result a) -> IO (Result a)
resetVM (IO m) = IO \s1 ->
  case reset# (\s2 -> case m s2 of (# s3, BoxResult r #) -> (# s3, r #)) s1 of
    (# s2, r #) -> (# s2, BoxResult r #)
{-# INLINE resetVM #-}

shiftVM :: (Continuation a b -> IO (Result b)) -> IO (Registers, a)
shiftVM f = IO \s1 -> case shift# f# s1 of (# s2, (# rs, a #) #) -> (# s2, (BoxRegisters rs, a) #)
  where
    f# k# s1 =
      let !k = Continuation# \a rs -> applyContinuation# k# (\s2 -> (# s2, (# rs, a #) #))
      in case unIO (f k) s1 of (# s2, BoxResult r #) -> (# s2, r #)
{-# INLINE shiftVM #-}

-- TODO: Share some code between `parameterizeVM` and `handle`.
parameterizeVM :: (Registers -> Registers) -> EVM a -> EVM a
parameterizeVM adjust (EVM m) = EVM \rs -> do
  resetVM (uncurry Return <$> m (adjust rs)) >>= \case
    Return _ a -> pure (rs, a)
    Capture target f k1 -> shiftVM \k2 -> pure $! handleCapture target f k1 k2
  where
    handleCapture
      :: PromptId
      -> ((a -> EVM d) -> EVM d)
      -> Continuation a b
      -> Continuation b c
      -> Result c
    handleCapture target1 f1 k1 k2 =
      let k3 a rs1 = do
            resetVM (runContinuation k1 a (adjust rs1)) >>= \case
              Return _ b -> runContinuation k2 b rs1
              Capture target2 f2 k4 -> pure $! handleCapture target2 f2 k4 k2
      in Capture target1 f1 (Continuation k3)

-- -------------------------------------------------------------------------------------------------

newtype Targets# = Targets# (SmallArray# Any)
newtype Targets = Targets (SmallArray Any)
pattern BoxTargets :: Targets# -> Targets
pattern BoxTargets ts <- Targets (SmallArray (Targets# -> ts))
  where BoxTargets (Targets# ts) = Targets (SmallArray ts)
{-# COMPLETE BoxTargets #-}

noTargets :: Targets
noTargets = Targets mempty

lookupTarget :: forall effs eff. (DebugCallStack, eff :< effs) => Targets -> Handler eff
lookupTarget (Targets ts) = case indexSmallArray ts (reifyIndex @eff @effs) of (# Any h #) -> h

pushTarget :: Handler eff -> Targets -> Targets
pushTarget !h (Targets ts1) = Targets $ runSmallArray do
  let len = sizeofSmallArray ts1
  ts2 <- newSmallArray (len + 1) null#
  writeSmallArray ts2 0 (Any h)
  copySmallArray ts2 1 ts1 0 len
  pure ts2

dropTargets :: DebugCallStack => Int -> Targets -> Targets
dropTargets idx (Targets ts) = Targets $ cloneSmallArray ts idx (sizeofSmallArray ts - idx)

-- -------------------------------------------------------------------------------------------------

instance Functor EVM where
  fmap f m = m >>= pure . f
  {-# INLINE fmap #-}

instance Applicative EVM where
  pure a = EVM# \rs s -> (# s, rs, a #)
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad EVM where
  EVM# m >>= f = EVM# \rs1 s1 -> case m rs1 s1 of (# s2, rs2, a #) -> unEVM# (f a) rs2 s2
  {-# INLINE (>>=) #-}

instance MonadIO EVM where
  liftIO (IO m) = EVM# \rs s1 -> case m s1 of (# s2, a #) -> (# s2, rs, a #)
  {-# INLINE liftIO #-}

-- -------------------------------------------------------------------------------------------------

run :: Eff '[] a -> a
run (Eff m) = unsafeDupablePerformIO (snd <$> m initialRegisters)

lift :: forall effs1 effs2. effs1 :<< effs2 => Eff effs1 ~> Eff effs2
lift (Eff# m) = Eff# (parameterizeVM adjustTargets m) where
  adjustTargets (Registers pid ts) = Registers pid (dropTargets (reifySubIndex @effs1 @effs2) ts)

-- | Like 'lift', but restricted to introducing a single additional effect in the result. This is
-- behaviorally identical to just using 'lift', but the restricted type can produce better type
-- inference.
lift1 :: forall eff effs. Eff effs ~> Eff (eff ': effs)
lift1 = lift
{-# INLINE lift1 #-}

-- -------------------------------------------------------------------------------------------------
-- Handling

data Handler eff = Handler { runHandler :: forall effs. eff (Eff effs) ~> Eff effs }

type Handling :: Effect -> [Effect] -> Type -> [Effect] -> Constraint
class Handling eff effs i effs' | eff effs' -> i effs where
  reifyHandlerContext :: HandlerContext
type instance DictRep (Handling _ _ _ _) = HandlerContext

data HandlerContext
  -- The Targets field needs to be lazy, as it involves a small bit of knot-tying: the Handler
  -- closure stored in the Targets references the HandlerContext, and the simplest place to break
  -- the cycle is here.
  = HandlerContext PromptId ~Targets

-- -------------------------------------------------------------------------------------------------

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \rs@(Registers _ ts) -> unEff (runHandler (lookupTarget @effs ts) e) rs

handle
  :: forall eff a effs
   . (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f (Eff m1) = Eff# (handleVM (fmap (uncurry Return) . m1))
  where
    handleVM :: (Registers -> IO (Result a)) -> EVM a
    handleVM m2 = EVM \rs1 -> do
      let !rs2@(Registers pid _) = pushPrompt rs1
      resetPrompt rs1 pid (m2 rs2) >>= \case
        Return _ a -> pure (rs1, a)
        Capture target g k1 -> shiftVM \k2 -> pure $! handleCaptureElsewhere target g k1 k2

    pushPrompt (Registers pid1 ts1) =
      let pid2 = PromptId (unPromptId pid1 + 1)
          hf :: forall effs'. eff (Eff effs') ~> Eff effs'
          hf = reflectDict @(Handling eff effs a effs') (HandlerContext pid2 ts2) f
          ts2 = pushTarget (Handler hf) ts1
      in Registers pid2 ts2

    -- Note: we have to be careful to push the catch frame /before/ pushing the reset frame, since
    -- we don’t want the abort handler in the captured continuation.
    resetPrompt rs pid m = handleCaptureHere =<< handleAbort (resetVM m) where
      handleAbort = flip IO.catch \exn@(AbortException target (Any a)) ->
        if unPromptId target == unPromptId pid
          then pure $! Return rs a
          else IO.throwIO exn

      handleCaptureHere = \case
        Capture target (g :: (b -> EVM c) -> EVM c) k1
          | unPromptId target == unPromptId pid ->
              -- We’re capturing up to this prompt, so the metacontinuation’s result type must be
              -- this function’s result type. (The thing that (indirectly) enforces this is the
              -- `Handling` constraint on `shift`.)
              with (axiom @a @c) do
                uncurry Return <$> unEVM (g (handleVM . runContinuation k1)) rs
        result -> pure result

    handleCaptureElsewhere
      :: PromptId
      -> ((b -> EVM d) -> EVM d)
      -> Continuation b a
      -> Continuation a c
      -> Result c
    handleCaptureElsewhere target1 f1 k1 k2 =
      let k3 a rs1 = do
            let !rs2@(Registers pid _) = pushPrompt rs1
            resetPrompt rs1 pid (runContinuation k1 a rs2) >>= \case
              Return _ b -> runContinuation k2 b rs1
              Capture target g k4 -> pure $! handleCaptureElsewhere target g k4 k2
      in Capture target1 f1 (Continuation k3)

liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff# m) = Eff# (parameterizeVM (\(Registers pid _) -> Registers pid ts) m) where
  HandlerContext _ ts = reifyHandlerContext @eff @effs @i @effs'

abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
abort a = Eff \_ -> do
  let !(HandlerContext target _) = reifyHandlerContext @eff @effs @i @effs'
  IO.throwIO $! AbortException target (Any a)

-- shift
--   :: forall eff effs i effs' a. Handling eff effs i effs'
--   => ((a -> Eff effs i) -> Eff effs i) -> Eff effs' a
-- shift f = Eff \_ _ -> do
--   let !(HandlerContext target _) = reifyHandlerContext @eff @effs @i @effs'
--   IO.shift \k# -> do
--     let k a = Eff \_ _ -> IO.applyContinuation k# (pure a)
--     pure $! Capture target k f

-- -------------------------------------------------------------------------------------------------

-- TODO: Fuse uses of swizzleTargets using RULES.
class Swizzle effs1 effs2 where
  swizzleTargets :: Targets -> Targets
instance {-# INCOHERENT #-} effs1 :<< effs2 => Swizzle effs1 effs2 where
  swizzleTargets = dropTargets (reifySubIndex @effs1 @effs2)
  {-# INLINE swizzleTargets #-}
instance Swizzle '[] effs where
  swizzleTargets _ = noTargets
  {-# INLINE swizzleTargets #-}
instance (eff :< effs2, Swizzle effs1 effs2) => Swizzle (eff ': effs1) effs2 where
  swizzleTargets ts = pushTarget (lookupTarget @effs2 @eff ts) $! swizzleTargets @effs1 @effs2 ts

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
-- swizzle :: forall effs1 effs2. Swizzle effs1 effs2 => Eff effs1 ~> Eff effs2
-- swizzle = wind winder where
--   winder = Winder \_ ts -> pure (swizzleTargets @effs1 @effs2 ts, unwinder)
--   unwinder = Unwinder pure (pure ()) (pure winder)
-- {-# INLINE swizzle #-}
