{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnboxedSums #-}

module Control.Effect.Internal where

import qualified Control.Exception as IO

import Control.Applicative
import Control.Exception (Exception)
import Control.Monad
import Control.Monad.IO.Class
import Control.Natural (type (~>))
import Data.Bool (bool)
import Data.IORef
import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:)(..), gcastWith)
import GHC.Exts (Any, Int(..), Int#, RealWorld, SmallArray#, State#, TYPE, reset#, shift#, applyContinuation#)
import GHC.Types (IO(..))
import System.IO.Unsafe (unsafeDupablePerformIO)
import Unsafe.Coerce (unsafeCoerce)

import Control.Effect.Internal.Debug
import Control.Effect.Internal.SmallArray

-- -------------------------------------------------------------------------------------------------

axiom :: a :~: b
axiom = unsafeCoerce Refl
{-# INLINE axiom #-}

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

-- | The kind of effects.
type Effect = (Type -> Type) -> Type -> Type

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

-- -------------------------------------------------------------------------------------------------

{- Note [The Eff Machine]
~~~~~~~~~~~~~~~~~~~~~~~~~
The Eff monad is best thought of as a “embedded virtual machine.” Given
primitive support for continuation manipulation from the host, Eff efficiently
implements a complement of complex control operations.

At any time, the Eff machine conceptually manages two pieces of state:

  1. The /metacontinuation stack/, which holds metacontinuation frames.
     Metacontinuation frames correspond to things like effect handlers,
     “thread-local” state, and dynamic winders.

  2. The /targets vector/, which maps a list of effects to the corresponding
     metacontinuation frames that handle them.

However, the representation of the metacontinuation stack is not explicit: it is
implicitly encoded as stack frames on the ordinary GHC RTS stack that cooperate
using a particular calling convention.

Note [Manual worker/wrapper]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
GHC performs an optimization called the /worker-wrapper transformation/, which
is used to propagate strictness information, unboxing, and more. The idea is
simple: if a function strictly operates on a boxed value, like

  f :: Int -> Foo
  f !n = ...

then GHC will internally rewrite it into a pair of definitions, a /worker/ and a
/wrapper/:

  $wf :: Int# -> Foo
  $wf n = ...

  f :: Int -> Foo
  f (I# n) = $wf n
  {-# INLINE f #-}

If some other code uses f, the wrapper will be inlined at the call site, and the
exposed unfolding allows GHC to make a direct call to $wf passing an unboxed
Int#.

This is great, but the automatic transformation can only do so much. The
worker/wrapper transformation relies on inlining, so it only works for known
calls. This means it can be advantageous to /manually/ perform this kind of
transformation to ensure unboxing happens, especially on datatypes (where the
“worker” is the datatype definition itself and the “wrapper” is a pattern
synonym.) -}

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
pattern PromptId{unPromptId} <- PromptId# (I# -> unPromptId)
  where PromptId (I# n) = PromptId# n
{-# COMPLETE PromptId #-}

data AbortException = AbortException PromptId ~Any
instance Show AbortException where
  show (AbortException _ _) = "AbortException"
instance Exception AbortException

newtype Result# a = Result# (# a | (# PromptId, Any, Any #) #)
data Result a = BoxResult (Result# a)
pattern Return :: a -> Result a
pattern Return a = BoxResult (Result# (# a | #))
pattern Capture
  :: PromptId
  -- ^ The prompt to capture up to.
  -> ((b -> EVM c) -> EVM c)
  -- ^ The metacontinuation passed by the user to the original call to 'shift'. This should be
  -- invoked with the fully-composed continuation after capturing is complete.
  -> Continuation b a
  -- ^ The composed continuation captured so far.
  -> Result a
pattern Capture pid f k = BoxResult (Result# (# | (# pid, Any f, Any k #) #))
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
  resetVM (Return . snd <$> m (adjust rs)) >>= \case
    Return a -> pure (rs, a)
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
              Return b -> runContinuation k2 b rs1
              Capture target2 f2 k4 -> pure $! handleCapture target2 f2 k4 k2
      in Capture target1 f1 (Continuation k3)
{-# INLINE parameterizeVM #-}

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

type Handle :: Effect -> [Effect] -> Type -> [Effect] -> Type -> Type
type role Handle nominal nominal representational nominal representational
newtype Handle eff effs i effs' a = Handle# { runHandle# :: Registers# -> Eff effs' a }
pattern Handle :: (Registers -> Eff effs' a) -> Handle eff effs i effs' a
pattern Handle{runHandle} <- Handle# ((\f (BoxRegisters rs) -> f rs) -> runHandle)
  where Handle f = Handle# \rs -> f (BoxRegisters rs)
{-# COMPLETE Handle #-}

instance Functor (Handle eff effs i effs') where
  fmap f m = m >>= pure . f
  {-# INLINE fmap #-}

instance Applicative (Handle eff effs i effs') where
  pure a = Handle# \_ -> pure a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Handle eff effs i effs') where
  Handle# m >>= f = Handle# \rs -> m rs >>= \a -> runHandle# (f a) rs
  {-# INLINE (>>=) #-}

newtype Handler eff
  = Handler { runHandler :: forall effs. eff :< effs => eff (Eff effs) ~> Eff effs }

-- -------------------------------------------------------------------------------------------------

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \rs@(Registers _ ts) -> unEff (runHandler (lookupTarget @effs ts) e) rs

handle
  :: forall eff a effs
   . (forall effs'. eff :< effs' => eff (Eff effs') ~> Handle eff effs a effs')
  -- ^ The handler function.
  -> Eff (eff ': effs) a
  -- ^ The action to handle.
  -> Eff effs a
handle f (Eff m1) = Eff# (handleVM (fmap (Return . snd) . m1))
  where
    handleVM :: (Registers -> IO (Result a)) -> EVM a
    handleVM m2 = EVM \rs1 -> do
      let !rs2@(Registers pid _) = pushPrompt rs1
      resetPrompt rs1 pid (m2 rs2) >>= \case
        Return a -> pure (rs1, a)
        Capture target g k1 -> shiftVM \k2 -> pure $! handleCaptureElsewhere target g k1 k2

    pushPrompt (Registers pid1 ts1) =
      let pid2 = PromptId (unPromptId pid1 + 1)
          h = Handler \e -> runHandle (f e) rs2
          ts2 = pushTarget h ts1
          rs2 = Registers pid2 ts2
      in rs2

    -- Note: we have to be careful to push the catch frame /before/ pushing the reset frame, since
    -- we don’t want the abort handler in the captured continuation.
    resetPrompt rs pid m = handleCaptureHere =<< handleAbort (resetVM m) where
      handleAbort = flip IO.catch \exn@(AbortException target (Any a)) ->
        if unPromptId target == unPromptId pid
          then pure $! Return a
          else IO.throwIO exn

      handleCaptureHere = \case
        Capture target (g :: (b -> EVM c) -> EVM c) k1
          | unPromptId target == unPromptId pid ->
              -- We’re capturing up to this prompt, so the metacontinuation’s result type must be
              -- this function’s result type.
              gcastWith (axiom @a @c) do
                Return . snd <$> unEVM (g (handleVM . runContinuation k1)) rs
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
              Return b -> runContinuation k2 b rs1
              Capture target g k4 -> pure $! handleCaptureElsewhere target g k4 k2
      in Capture target1 f1 (Continuation k3)

locally :: Eff effs' ~> Handle eff effs i effs'
locally m = Handle \_ -> m

liftH :: Eff (eff ': effs) ~> Handle eff effs i effs'
liftH (Eff# m) = Handle \(Registers _ ts) ->
  Eff# (parameterizeVM (\(Registers pid _) -> Registers pid ts) m)

abort :: i -> Handle eff effs i effs' a
abort a = Handle \(Registers pid _) -> Eff \_ -> IO.throwIO $! AbortException pid (Any a)

shift :: ((a -> Eff effs i) -> Eff effs i) -> Handle eff effs i effs' a
shift f = Handle \(Registers pid _) -> Eff \_ ->
  shiftVM \k1 -> pure $! Capture pid (\k2 -> unEff# (f (Eff# . k2))) k1

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
swizzle = Eff# . parameterizeVM adjustTargets . unEff# where
  adjustTargets (Registers pid ts) = Registers pid (swizzleTargets @effs1 @effs2 ts)

-- -------------------------------------------------------------------------------------------------

data IOE :: Effect where
  LiftIO :: IO a -> IOE m a

unsafeIOToEff :: IO ~> Eff effs
unsafeIOToEff = Eff# . liftIO
{-# INLINE unsafeIOToEff #-}

runIO :: Eff '[IOE] ~> IO
runIO m0 = snd <$> unEff (handleIO m0) initialRegisters where
  handleIO = handle \case
    LiftIO m -> locally (unsafeIOToEff m)

instance IOE :< effs => MonadIO (Eff effs) where
  liftIO = send . LiftIO
  {-# INLINE liftIO #-}

-- -------------------------------------------------------------------------------------------------

data State s :: Effect where
  Get :: State s m s
  Put :: ~s -> State s m ()

evalState :: forall s effs. s -> Eff (State s ': effs) ~> Eff effs
evalState s0 (Eff m) = Eff \rs -> do
  ref <- newIORef s0
  resetVM (Return . snd <$> m (pushHandler ref rs)) >>= \case
    Return a -> pure (rs, a)
    Capture target f k1 -> shiftVM \k2 -> handleCapture ref target f k1 k2
  where
    pushHandler ref (Registers pid ts) =
      let h :: Handler (State s)
          h = Handler \case
            Get -> Eff# $ liftIO $ readIORef ref
            Put !s -> Eff# $ liftIO $ writeIORef ref s
      in Registers pid (pushTarget h ts)

    handleCapture
      :: IORef s
      -> PromptId
      -> ((a -> EVM d) -> EVM d)
      -> Continuation a b
      -> Continuation b c
      -> IO (Result c)
    handleCapture ref1 target1 f1 k1 k2 = do
      s <- readIORef ref1
      let k3 a rs1 = do
            ref2 <- newIORef s
            resetVM (runContinuation k1 a (pushHandler ref2 rs1)) >>= \case
              Return b -> runContinuation k2 b rs1
              Capture target2 f2 k4 -> handleCapture ref2 target2 f2 k4 k2
      pure $! Capture target1 f1 (Continuation k3)

-- -------------------------------------------------------------------------------------------------

data NonDet :: Effect where
  Empty :: NonDet m a
  Choose :: NonDet m Bool

instance NonDet :< effs => Alternative (Eff effs) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send Choose >>= bool b a
  {-# INLINE (<|>) #-}
