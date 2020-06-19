{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal where

import qualified Control.Exception as IO
import qualified Data.Type.Coercion as Coercion

import Control.Applicative
import Control.Exception (Exception)
import Control.Monad
import Control.Monad.IO.Class
import Data.Bool (bool)
import Data.Coerce
import Data.Functor
import Data.IORef
import Data.Kind (Constraint, Type)
import Data.Type.Coercion (Coercion(..), gcoerceWith)
import Data.Type.Equality ((:~:)(..), gcastWith)
import GHC.Exts (Any, Int(..), Int#, RealWorld, RuntimeRep(..), SmallArray#, State#, TYPE, reset#, shift#)
import GHC.Types (IO(..))
import System.IO.Unsafe (unsafeDupablePerformIO)
import Unsafe.Coerce (unsafeCoerce)

import Control.Effect.Internal.Debug
import Control.Effect.Internal.SmallArray

-- -----------------------------------------------------------------------------

axiom :: a :~: b
axiom = unsafeCoerce Refl
{-# INLINE axiom #-}

-- | A restricted form of 'unsafeCoerce' that only works for converting to/from
-- 'Any'. Still just as unsafe, but makes it slightly more difficult to
-- accidentally misuse.
pattern Any :: forall a. a -> Any
pattern Any a <- (unsafeCoerce -> a)
  where Any = unsafeCoerce
{-# COMPLETE Any #-}

anyCo :: forall a. Coercion a Any
anyCo = unsafeCoerce (Coercion @a @a)
{-# INLINE anyCo #-}

-- | Used to explicitly overwrite references to values that should not be
-- retained by the GC.
null# :: Any
null# = Any ()

unIO :: IO a -> State# RealWorld -> (# State# RealWorld, a #)
unIO (IO m) = m
{-# INLINE unIO #-}

-- -----------------------------------------------------------------------------

data Dict c = c => Dict

type DictRep :: Constraint -> Type
type family DictRep c

type WithDict :: Constraint -> Type -> Type
newtype WithDict c r = WithDict { unWithDict :: c => r }

reflectDict :: forall c r. DictRep c -> (c => r) -> r
reflectDict !d x = unsafeCoerce (WithDict @c @r x) d
{-# INLINE reflectDict #-}

-- -----------------------------------------------------------------------------

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

type instance DictRep (eff :< effs) = Int
type instance DictRep (effs1 :<< effs2) = Int

type (:<#) :: Effect -> [Effect] -> TYPE 'IntRep
-- see Note [Manual worker/wrapper]
newtype eff :<# effs = ReflectIndex# { reifyIndex# :: Int# }
pattern IndexDict# :: forall eff effs. () => eff :< effs => eff :<# effs
pattern IndexDict# <- ReflectIndex# ((\idx -> reflectDict @(eff :< effs) (I# idx) (Dict @(eff :< effs))) -> Dict)
  where IndexDict# = case reifyIndex @eff @effs of I# idx -> ReflectIndex# idx
{-# COMPLETE IndexDict# #-}

{- -----------------------------------------------------------------------------
-- Note [The Eff Machine]
~~~~~~~~~~~~~~~~~~~~~~~~~
The Eff monad is best thought of as a “embedded virtual machine.” Given
primitive support for continuation manipulation from the host, Eff efficiently
implements a complement of complex control operations.

At any time, the Eff machine conceptually manages two pieces of state:

  1. The /metacontinuation stack/, which holds metacontinuation frames.
     Metacontinuation frames correspond to things like effect handlers,
     “thread-local” state, and dynamic winders.

  2. The /targets vector/, which maps a list of effects to the corresponding
     metacontinuation frames that handle them. (See Note [The targets vector].)

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

-- | All @eff@ computations operate in the 'Eff' monad. 'Eff' computations are
-- parameterized by a type-level list that specifies which effects they are
-- allowed to perform. For example, a computation of type
-- @'Eff' '['Control.Effect.Error' e, 'Control.Effect.Reader' r, 'Control.Effect.State' s] a@
-- can raise exceptions of type @e@, can access a global environment of type
-- @r@, and can read and modify a single cell of mutable state of type @s@.
--
-- To run an 'Eff' computation that performs effects, the effects must be
-- explicitly /handled/. Functions that handle effects are called
-- /effect handlers/, and they usually have types like the following:
--
-- @
-- runX :: 'Eff' (X ': effs) a -> 'Eff' effs a
-- @
--
-- Note that the argument to @runX@ can perform the @X@ effect, but the result
-- cannot! Any @X@ operations have been handled by @runX@, which interprets
-- their meaning. Examples of effect handlers include
-- 'Control.Effect.Error.runError', 'Control.Effect.Reader.runReader', and
-- 'Control.Effect.State.Strict.runState'.
--
-- After all effects have been handled, the resulting computation will have type
-- @'Eff' '[] a@, a computation that performs no effects. A computation with
-- this type is pure, so it can be converted to an ordinary value using 'run'.
--
-- Some effects cannot be handled locally, but instead require performing I/O.
-- These effects will delegate to the 'IOE' effect, which provides low-level
-- interop with Haskell’s built-in 'IO' monad. After all other effects have been
-- handled, a computation of type @'Eff' '['IOE'] a@ can be converted to an
-- ordinary @'IO' a@ computation using 'runIO'.
type Eff :: [Effect] -> Type -> Type
type role Eff nominal representational
newtype Eff effs a = Eff# { unEff# :: EVM a }
  deriving (Functor, Applicative, Monad)

pattern Eff :: (Registers -> IO (Registers, a)) -> Eff effs a
pattern Eff{unEff} = Eff# (EVM unEff) -- see Note [Manual worker/wrapper]
{-# COMPLETE Eff #-}

newtype EVM a = EVM# { unEVM# :: Registers# -> IO (Result a) }
data Result a = Result Registers# ~a

pattern EVM :: (Registers -> IO (Registers, a)) -> EVM a
-- see Note [Manual worker/wrapper]
pattern EVM{unEVM} <- EVM# ((\m (BoxRegisters rs1) -> m rs1 <&> \(Result rs2 a) -> (BoxRegisters rs2, a)) -> unEVM)
  where EVM m = EVM# \rs1 -> m (BoxRegisters rs1) <&> \(BoxRegisters rs2, a) -> Result rs2 a
{-# COMPLETE EVM #-}

packIOResult :: IO (Registers, a) -> IO (Result a)
-- see Note [Manual worker/wrapper]
packIOResult m = m >>= \(BoxRegisters rs, a) -> pure $! Result rs a
{-# INLINE packIOResult #-}

-- -----------------------------------------------------------------------------

newtype Registers# = Registers# (# PromptId, Targets# #)
data Registers = BoxRegisters { unboxRegisters :: Registers# }
pattern Registers :: PromptId -> Targets -> Registers
-- see Note [Manual worker/wrapper]
pattern Registers pid ts <- BoxRegisters (Registers# (# pid, (BoxTargets -> ts) #))
  where Registers pid (BoxTargets ts) = BoxRegisters (Registers# (# pid, ts #))
{-# COMPLETE Registers #-}

initialRegisters :: Registers
initialRegisters = Registers (PromptId 0) noTargets

newtype PromptId = PromptId# Int#
pattern PromptId :: Int -> PromptId
-- see Note [Manual worker/wrapper]
pattern PromptId{unPromptId} <- PromptId# (I# -> unPromptId)
  where PromptId (I# n) = PromptId# n
{-# COMPLETE PromptId #-}

data Unwind
  = UnwindAbort PromptId ~Any
  | UnwindControl (Capture Any) -- TODO: unpack?

instance Show Unwind where
  show (UnwindAbort (PromptId pid) _)
    = "<<Control.Eff.Internal.abort:" ++ show pid ++ ">>"
  show (UnwindControl (Capture (PromptId pid) _ _))
    = "<<Control.Eff.Internal.control:" ++ show pid ++ ">>"
instance Exception Unwind

data Capture a where
  Capture
    :: PromptId
    -- ^ The prompt to capture up to.
    -> ((b -> EVM c) -> EVM c)
    -- ^ The replacement continuation passed by the user to the original call to
    -- 'control'. This should be invoked with the fully-composed continuation
    -- after capturing is complete.
    -> (b -> EVM a)
    -- ^ The composed continuation captured so far.
    -> Capture a

captureVM :: forall a b. Capture a -> IO b
captureVM a = gcoerceWith (Coercion.sym $ anyCo @a) $
  IO.throwIO $! UnwindControl (coerce a)
{-# INLINE captureVM #-}

-- | Runs an 'EVM' action with a new prompt installed. The arguments specify
-- what happens when control exits the action.
promptVM
  :: forall a
   . IO (Registers, a)
  -> Registers
  -- ^ registers to restore on a normal return
  -> (PromptId -> Any -> IO (Registers, a))
  -- ^ abort handler
  -> (Capture a -> IO (Registers, a))
  -- ^ control handler
  -> IO (Registers, a)
promptVM m rs onAbort onControl = IO.handle handleUnwind do
  -- TODO: Explain why it is crucial that the exception handler is installed
  -- outside of the frame where we replace the registers!
  Result _ a <- IO (reset# (unIO (packIOResult m)))
  pure (rs, a)
  where
    handleUnwind (UnwindAbort pid a) = onAbort pid a
    handleUnwind (UnwindControl cap) = gcoerceWith (anyCo @a) $ onControl (coerce cap)
{-# INLINE promptVM #-}

-- | Like 'promptVM', but for prompts that cannot be the target of an abort.
promptVM_
  :: forall a
   . IO (Registers, a)
  -> Registers
  -> (Capture a -> IO (Registers, a))
  -> IO (Registers, a)
promptVM_ m rs f = promptVM m rs rethrowAbort f where
  -- TODO: Check if this unwrapping/rewrapping is eliminated at the STG level.
  rethrowAbort pid a = IO.throwIO $! UnwindAbort pid a
{-# INLINE promptVM_ #-}

controlVM :: ((a -> EVM b) -> IO (Registers, b)) -> IO (Registers, a)
controlVM f = IO (shift# f#) <&> \(Result rs a) -> (BoxRegisters rs, a) where
  f# k# = unIO (f k <&> \(BoxRegisters rs, a) -> Result rs a) where
    k a = EVM# \rs -> IO $ k# \s -> (# s, Result rs a #)
{-# INLINE controlVM #-}

-- TODO: Share some code between `parameterizeVM` and `handle`.
parameterizeVM :: (Registers -> Registers) -> EVM a -> EVM a
parameterizeVM adjust (EVM m) = EVM \rs -> do
  promptVM_ (m (adjust rs)) rs \(Capture target f k1) ->
    controlVM \k2 -> captureVM $! handleCapture target f k1 k2
  where
    handleCapture
      :: PromptId
      -> ((a -> EVM d) -> EVM d)
      -> (a -> EVM b)
      -> (b -> EVM c)
      -> Capture c
    handleCapture target1 f1 k1 k2 =
      let k3 a = EVM \rs1 -> do
            (rs2, b) <- promptVM_ (unEVM (k1 a) (adjust rs1)) rs1 \(Capture target2 f2 k4) ->
              captureVM $! handleCapture target2 f2 k4 k2
            unEVM (k2 b) rs2
      in Capture target1 f1 k3
{-# INLINE parameterizeVM #-}

{- -----------------------------------------------------------------------------
-- Note [The targets vector]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In most implementations of delimited control or algebraic effects, handling an
effect involves walking the prompt/handler stack looking for a frame with the
right tag. This is a little unfortunate, as in the large majority of use cases,
the handler stack changes infrequently relative to the number of effectful
operations that are performed. Therefore, we take a slightly different approach,
and we cache which effects are handled by which handlers at any given time.

This cache is stored in the /targets vector/ (represented by type `Targets`), an
immutable SmallArray that contains pointers to `Handler`s. Each effect is mapped
to a handler using its index in the type-level list. For example, if we have a
computation of type

    Eff '[Reader Int, NonDet, Error String] a

then the targets vector will be three elements long. Index 0 will point to a
handler for `Reader Int`, index 1 will point to a handler for `NonDet`, and
index 2 will point to a handler for `Error String`.

The targets vector makes `send` a constant-time operation, regardless of the
number of effects. The `:<` class provides the effect’s index, so `send` need
only look up the index in the targets vector and invoke the handler. This is a
particularly good tradeoff in situations where the following conditions hold:

  1. Most effects are handled at the top-level of the program and changed
     infrequently during runtime.

  2. Most calls to `send` do not need to capture the continuation.

In practice, these conditions seem usually true. However, if they aren’t,
maintaining the targets vector has a cost: it needs to be recomputed on every
use of `handle` or `lift`, and continuation restore requires recomputing the
vector for every `handle` or `lift` frame in the captured continuation! In most
cases, the vector is very small, so this isn’t a big deal.

If the overhead of maintaining the targets vector ever turns out to be
significant, there are a variety of potential optimizations that we currently
don’t do. Here are a couple possibilities:

  * Most continuations are restored in the same context where they’re captured,
    so there’s no need to recompute the targets vectors upon restore. Skipping
    is the recomputation in that case is likely a particularly easy win.

  * If the list of effects grows very large, the cost of copying the whole
    vector could become prohibitive. In those situations, we could switch to a
    more sophisticated representation that allows more sharing while still
    providing decent access time, avoiding the need for unbounded copying. -}

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
pushTarget h (Targets ts1) = Targets $ runSmallArray do
  let len = sizeofSmallArray ts1
  ts2 <- newSmallArray (len + 1) null#
  writeSmallArray ts2 0 (Any h)
  copySmallArray ts2 1 ts1 0 len
  pure ts2

dropTargets :: DebugCallStack => Int -> Targets -> Targets
dropTargets idx (Targets ts) = Targets $ cloneSmallArray ts idx (sizeofSmallArray ts - idx)

-- -----------------------------------------------------------------------------

instance Functor EVM where
  fmap f m = m >>= pure . f
  {-# INLINE fmap #-}

instance Applicative EVM where
  pure a = EVM# \rs -> pure $ Result rs a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad EVM where
  EVM# m >>= f = EVM# \rs1 -> m rs1 >>= \(Result rs2 a) -> unEVM# (f a) rs2
  {-# INLINE (>>=) #-}

instance MonadIO EVM where
  liftIO m = EVM# \rs -> Result rs <$> m
  {-# INLINE liftIO #-}

-- | Runs a pure 'Eff' computation to produce a value.
--
-- @
-- >>> 'run' '$' 'pure' 42
-- 42
-- >>> 'run' '$' 'Control.Effect.Error.runError' '$' 'Control.Effect.Error.throw' "bang"
-- 'Left' "bang"
-- @
run :: Eff '[] a -> a
run (Eff m) = unsafeDupablePerformIO (snd <$> m initialRegisters)

-- -----------------------------------------------------------------------------

-- | The monad that effect handlers run in.
--
--   * The @eff@ parameter is the effect being handled, and the @effs@ parameter
--     includes the other effects in scope at the point of the 'handle' call
--     (used by 'liftH').
--
--   * The @i@ parameter is the return type of the handled computation (used by
--     'control' and 'abort').
--
--   * The @effs'@ parameter is the list of effects in scope at the point of the
--     originating 'send' call (used by 'locally').
--
-- See 'handle' for more details.
type Handle :: Effect -> [Effect] -> Type -> [Effect] -> Type -> Type
type role Handle nominal nominal representational nominal representational
newtype Handle eff effs i effs' a = Handle# { runHandle# :: Registers# -> Eff effs' a }
pattern Handle :: (Registers -> Eff effs' a) -> Handle eff effs i effs' a
-- see Note [Manual worker/wrapper]
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
  = Handler# { runHandler# :: forall effs a. eff :<# effs -> eff (Eff effs) a -> Eff effs a }
newtype WrappedHandler eff
  -- Unfortunately necessary to avoid the need for impredicative polymorphism in
  -- the definition of the Handler pattern synonym.
  = WrapHandler (forall effs a. eff :< effs => eff (Eff effs) a -> Eff effs a)
pattern Handler :: (forall effs a. eff :< effs => eff (Eff effs) a -> Eff effs a) -> Handler eff
-- see Note [Manual worker/wrapper]
pattern Handler{runHandler} <- ((\(Handler# f) -> WrapHandler (f IndexDict#)) -> WrapHandler runHandler)
  where Handler f = Handler# \IndexDict# -> f
{-# COMPLETE Handler #-}

-- -----------------------------------------------------------------------------

send :: forall eff a effs. eff :< effs => eff (Eff effs) a -> Eff effs a
send !e = Eff \rs@(Registers _ ts) -> unEff (runHandler (lookupTarget @effs ts) e) rs

-- | Handles the topmost effect in an 'Eff' computation. The given handler
-- function must provide an interpretation for each effectful operation. The
-- handler runs in the restrictive 'Handle' monad, which generally uses one of
-- the following core 'Handle' operations:
--
--   * 'liftH' — Runs an action in the context of the original 'handle' call.
--     This is the most common way to handle an effect.
--
--   * 'abort' — Aborts the computation to the 'handle' call and returns a value
--     directly. This is usually used to implement exception-like operations.
--
--   * 'control' — Captures the current continuation up to the 'handle' call and
--     aborts, passing the captured continuation to the handler. This can be
--     used to implement complex control operators such as coroutines or
--     resumable exceptions.
--
--   * 'locally' — Runs an action directly in the context of the originating
--     'send' call. This can be used to implement “scoped” operations like
--     'Control.Effect.local' and 'Control.Effect.catch'.
--
-- See the documentation for each of the above functions for examples and more
-- details.
handle
  :: forall eff a effs
   . (forall effs' b. eff :< effs' => eff (Eff effs') b -> Handle eff effs a effs' b)
  -- ^ The handler function.
  -> Eff (eff ': effs) a
  -- ^ The action to handle.
  -> Eff effs a
handle f = handleVM \rs -> Handler \e -> runHandle# (f e) rs
{-# INLINE handle #-}

handleVM :: forall eff a effs. (Registers# -> Handler eff) -> Eff (eff ': effs) a -> Eff effs a
handleVM f (Eff m1) = Eff# (withHandler m1)
  where
    withHandler :: (Registers -> IO (Registers, a)) -> EVM a
    -- GHC can’t figure out how to pull this small bit of unboxing out of the
    -- recursive knot we’re tying, so we do it manually here
    withHandler g = withHandler# (unEVM# (EVM g))
    {-# INLINE withHandler #-}

    withHandler# :: (Registers# -> IO (Result a)) -> EVM a
    withHandler# m2 = EVM \rs -> do
      resetPrompt (EVM# m2) rs \(Capture target g k1) ->
        controlVM \k2 -> captureVM $! handleCaptureElsewhere target g k1 k2

    pushPrompt (Registers pid1 ts1) =
      let pid2 = PromptId (unPromptId pid1 + 1)
          ts2 = pushTarget (f (unboxRegisters rs2)) ts1
          rs2 = Registers pid2 ts2
      in rs2

    resetPrompt m rs1 onCaptureElsewhere =
      promptVM (unEVM m rs2) rs1 handleAbort handleCapture
      where
        !rs2@(Registers pid _) = pushPrompt rs1

        handleAbort target a
          | unPromptId target == unPromptId pid = case a of { Any b -> pure (rs1, b) }
          | otherwise = IO.throwIO $! UnwindAbort target a

        handleCapture = \case
          Capture target (g :: (b -> EVM c) -> EVM c) k1
            | unPromptId target == unPromptId pid ->
                -- We’re capturing up to this prompt, so the new continuation’s
                -- result type must be this function’s result type.
                gcastWith (axiom @a @c) do
                  unEVM (g (withHandler . unEVM . k1)) rs1
          cap -> onCaptureElsewhere cap

    handleCaptureElsewhere
      :: PromptId
      -> ((b -> EVM d) -> EVM d)
      -> (b -> EVM a)
      -> (a -> EVM c)
      -> Capture c
    handleCaptureElsewhere target1 f1 k1 k2 =
      let k3 a = EVM \rs1 -> do
            (rs2, b) <- resetPrompt (k1 a) rs1 \(Capture target g k4) ->
              captureVM $! handleCaptureElsewhere target g k4 k2
            unEVM (k2 b) rs2
      in Capture target1 f1 k3

locally :: Eff effs' a -> Handle eff effs i effs' a
locally m = Handle \_ -> m

liftH :: Eff (eff ': effs) a -> Handle eff effs i effs' a
liftH (Eff# m) = Handle \(Registers _ ts) ->
  Eff# (parameterizeVM (\(Registers pid _) -> Registers pid ts) m)

abort :: i -> Handle eff effs i effs' a
abort a = Handle \(Registers pid _) -> Eff \_ -> IO.throwIO $! UnwindAbort pid (Any a)

control :: ((a -> Eff effs i) -> Eff effs i) -> Handle eff effs i effs' a
control f = Handle \(Registers pid _) -> Eff \_ ->
  controlVM \k1 -> captureVM $! Capture pid (\k2 -> unEff# (f (Eff# . k2))) k1

-- -----------------------------------------------------------------------------

-- TODO: Fuse uses of liftTargets using RULES.
type Lift :: [Effect] -> [Effect] -> Constraint
class Lift effs1 effs2 where
  liftTargets :: Targets -> Targets
instance {-# INCOHERENT #-} effs1 :<< effs2 => Lift effs1 effs2 where
  liftTargets = dropTargets (reifySubIndex @effs1 @effs2)
  {-# INLINE liftTargets #-}
instance Lift '[] effs where
  liftTargets _ = noTargets
  {-# INLINE liftTargets #-}
instance (eff :< effs2, Lift effs1 effs2) => Lift (eff ': effs1) effs2 where
  liftTargets ts = pushTarget (lookupTarget @effs2 @eff ts) $! liftTargets @effs1 @effs2 ts

-- | Lifts an 'Eff' computation into one that performs all the same effects, and
-- possibly more. For example, if you have a computation
--
-- @
-- m :: 'Eff' '[Foo, Bar] ()
-- @
--
-- then 'lift' will transform it into a polymorphic computation with the
-- following type:
--
-- @
-- 'lift' m :: (Foo ':<' effs, Bar ':<' effs) => 'Eff' effs ()
-- @
--
-- This type is much more general, and @effs@ can now be instantiated at many
-- different types. Generally, 'lift' can manipulate the list of effects in any
-- of the following ways:
--
--   * Effects can be reordered.
--   * New effects can be inserted anywhere in the list.
--   * Duplicate effects can be collapsed.
--
-- More generally, the list of effects doesn’t need to be entirely concrete in
-- order for 'lift' to work. For example, if you have a computation
--
-- @
-- n :: 'Eff' (Foo ': Bar ': effs1) ()
-- @
--
-- then @'lift' n@ will have the following type:
--
-- @
-- 'lift' n :: (Foo ':<' effs2, Bar ':<' effs2, effs1 ':<<' effs2) => 'Eff' effs2 ()
-- @
--
-- This type is extremely general, and it allows 'lift' to manipulate the /head/
-- of the effects list even if the entire list is not completely known.
--
-- The 'Lift' typeclass provides some type-level programming machinery to
-- implement 'lift', but it should be treated as an implementation detail. In
-- most situations, the machinery should “just work,” but if it doesn’t, the
-- type errors can be somewhat inscrutable. In those situations, adding some
-- explicit type annotations (or using @TypeApplications@) can improve the type
-- errors significantly.
lift :: forall effs1 effs2 a. Lift effs1 effs2 => Eff effs1 a -> Eff effs2 a
lift = Eff# . parameterizeVM liftRegisters . unEff# where
  liftRegisters (Registers pid ts) = Registers pid (liftTargets @effs1 @effs2 ts)

-- | Like 'lift', but restricted to introducing a single additional effect in the result. This is
-- behaviorally identical to just using 'lift', but the restricted type can produce better type
-- inference.
lift1 :: forall eff effs a. Eff effs a -> Eff (eff ': effs) a
lift1 = lift
{-# INLINE lift1 #-}

-- -----------------------------------------------------------------------------

-- | An effect used to run 'IO' operations via 'liftIO'. Handled by the special
-- 'runIO' handler.
data IOE :: Effect where
  LiftIO :: IO a -> IOE m a

unsafeIOToEff :: IO a -> Eff effs a
unsafeIOToEff = Eff# . liftIO
{-# INLINE unsafeIOToEff #-}

-- | Converts an 'Eff' computation to 'IO'. Unlike most handlers, 'IOE' must be
-- the final effect handled, and 'runIO' completely replaces the call to 'run'.
runIO :: Eff '[IOE] a -> IO a
runIO m0 = snd <$> unEff (handleIO m0) initialRegisters where
  handleIO = handle \case
    LiftIO m -> locally (unsafeIOToEff m)

instance IOE :< effs => MonadIO (Eff effs) where
  liftIO = send . LiftIO
  {-# INLINE liftIO #-}

-- -----------------------------------------------------------------------------

-- | The @'State' s@ effect provides access to a single cell of mutable state of
-- type @s@.
data State s :: Effect where
  Get :: State s m s
  Put :: ~s -> State s m ()

evalState :: s -> Eff (State s ': effs) a -> Eff effs a
evalState (s0 :: s) (Eff m0) = Eff \rs -> do
  ref <- newIORef s0
  promptVM_ (m0 (pushHandler ref rs)) rs \(Capture target f k1) ->
    controlVM \k2 -> handleCapture ref target f k1 k2
  where
    pushHandler :: IORef s -> Registers -> Registers
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
      -> (a -> EVM b)
      -> (b -> EVM c)
      -> IO (Registers, b)
    handleCapture ref1 target1 f1 k1 k2 = do
      s <- readIORef ref1
      let k3 a = EVM \rs1 -> do
            ref2 <- newIORef s
            let m = unEVM (k1 a) (pushHandler ref2 rs1)
            (rs2, b) <- promptVM_ m rs1 \(Capture target2 f2 k4) ->
              handleCapture ref2 target2 f2 k4 k2
            unEVM (k2 b) rs2
      captureVM $! Capture target1 f1 k3

-- -----------------------------------------------------------------------------

-- | The 'NonDet' effect provides so-called /nondeterministic execution/, which
-- runs all branches of a computation and collects some or all of their results.
-- Actual execution is not usually truly nondeterministic in the sense that it
-- is somehow random; rather, 'NonDet' models nondeterministic binary choice by
-- executing /both/ possibilities rather than choosing just one.
data NonDet :: Effect where
  Empty :: NonDet m a
  Choose :: NonDet m Bool

instance NonDet :< effs => Alternative (Eff effs) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send Choose >>= bool b a
  {-# INLINE (<|>) #-}
