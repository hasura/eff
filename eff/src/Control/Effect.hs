{-| @eff@ is a fast, flexible, easy to use effect system for Haskell. @eff@
makes it easy to write composable, modular effects and effect handlers without
sacrificing performance. Broadly speaking, @eff@ provides the following
features:

  * The 'Eff' monad, which provides an extremely flexible set of control
    operations that can be used to implement a variety of effects.

  * A standard library of built-in effects and effect handlers, including common
    effects like 'Reader', 'State', and 'Error'.

  * A framework for defining your own effects and effect handlers, which can
    either be built from scratch using the 'Eff' primitives or by delegating to
    an existing handler.

@eff@ is far from the first effect system for Haskell, but it differentiates
itself from existing libraries in the following respects:

  * @eff@ is built atop a direct, low-level implementation of delimited
    continuations to provide the best performance possible.

  * @eff@ provides a simpler, more streamlined API for handling effects.

  * Like @polysemy@ and @fused-effects@ (but unlike @freer-simple@), @eff@
    supports so called “scoped” effect operations like 'local' and 'catch', but
    unlike @polysemy@ and @fused-effects@ (and also unlike
    @transformers@/@mtl@), @eff@ provides a consistent semantics for such
    operations regardless of handler order.

@eff@ aspires to be a turnkey replacement for most traditional uses of monad
transformers. @eff@ provides comparable performance to @transformers@ and @mtl@
with less complexity, less boilerplate, and a simpler semantics. -}
module Control.Effect (
  -- * The @Eff@ monad
    Eff
  , run
  , lift
  , lift1
  , swizzle

  -- * Defining new effects
  , Effect
  , (:<)
  , send

  -- * Handling effects
  -- ** Simple effect handlers
  , interpret
  -- ** Advanced effect handlers
  , Handle
  , handle
  , liftH
  , abort
  , shift
  , locally

  -- * Performing I/O
  , IOE(..)
  , MonadIO(..)
  , runIO

  -- * Built-in effects
  , Error(..)
  , throw
  , catch
  , runError

  , Reader(..)
  , ask
  , local
  , runReader

  , State(..)
  , get
  , put
  , modify
  , runState
  , evalState
  , execState

  , Writer(..)
  , tell
  , listen
  , censor
  , runWriter
  , evalWriter
  , execWriter

  , NonDet(..)
  , Alternative(..)
  , runNonDetAll

  , Coroutine(..)
  , yield
  , Status(..)
  , runCoroutine

  -- * Re-exports
  , (&)
  , (>>>)
  ) where

import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.IO.Class
import Data.Function
import Data.Tuple (swap)

import Control.Effect.Internal

-- | The simplest way to handle an effect. Each use of 'send' for the handled
-- effect dispatches to the handler function, which provides an interpretation
-- for the operation. The handler function may handle the operation directly, or
-- it may defer to other effects currently in scope.
--
-- Most effect handlers should be implemented using 'interpret', possibly with
-- the help of additional 'Error' or 'State' effects. Especially complex
-- handlers can be defined via the more general 'handle', which 'interpret' is
-- defined in terms of:
--
-- @
-- 'interpret' f = 'handle' ('liftH' '.' f)
-- @
interpret
  :: forall eff a effs
   . (forall m b. eff m b -> Eff (eff ': effs) b)
  -- ^ The handler function.
  -> Eff (eff ': effs) a
  -- ^ The action to handle.
  -> Eff effs a
interpret f = handle (liftH . f)

data Error e :: Effect where
  Throw :: e -> Error e m a
  Catch :: Eff (Error e ': effs) a -> (e -> Eff effs a) -> Error e (Eff effs) a

throw :: Error e :< effs => e -> Eff effs a
throw = send . Throw

catch :: Error e :< effs => Eff (Error e ': effs) a -> (e -> Eff effs a) -> Eff effs a
catch a b = send $ Catch a b

runError :: forall e a effs. Eff (Error e ': effs) a -> Eff effs (Either e a)
runError = fmap Right >>> handle \case
  Throw e -> abort $ Left e
  Catch m' f -> locally (either f pure =<< runError m')

data Reader r :: Effect where
  Ask :: Reader r m r
  Local :: (r1 -> r2) -> Eff (Reader r2 ': effs) a -> Reader r1 (Eff effs) a

ask :: Reader r :< effs => Eff effs r
ask = send Ask

local :: Reader r1 :< effs => (r1 -> r2) -> Eff (Reader r2 ': effs) a -> Eff effs a
local a b = send $ Local a b

runReader :: r -> Eff (Reader r ': effs) a -> Eff effs a
runReader r = handle \case
  Ask -> pure r
  Local f m -> locally let !r' = f r in runReader r' m

get :: State s :< effs => Eff effs s
get = send Get

put :: State s :< effs => s -> Eff effs ()
put = send . Put

modify :: State s :< effs => (s -> s) -> Eff effs ()
modify f = get >>= put . f

runState :: s -> Eff (State s ': effs) a -> Eff effs (s, a)
runState s m = evalState s (curry swap <$> m <*> get)

execState :: s -> Eff (State s ': effs) a -> Eff effs s
execState s m = evalState s (m *> get)

data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: Eff (Writer w ': effs) a -> Writer w (Eff effs) (w, a)
  Censor :: (w -> w) -> Eff (Writer w ': effs) a -> Writer w (Eff effs) a

tell :: Writer w :< effs => w -> Eff effs ()
tell = send . Tell

listen :: Writer w :< effs => Eff (Writer w ': effs) a -> Eff effs (w, a)
listen = send . Listen

censor :: Writer w :< effs => (w -> w) -> Eff (Writer w ': effs) a -> Eff effs a
censor a b = send $ Censor a b

runWriter :: Monoid w => Eff (Writer w ': effs) a -> Eff effs (w, a)
runWriter (m0 :: Eff (Writer w ': effs) a) = swizzle m0
  & handle \case
      Tell w -> liftH $ tellS w
      Listen m -> locally $ runListen m
      Censor f m -> locally $ runCensor f m
  & runState mempty
  where
    tellS :: State w :< effs' => w -> Eff effs' ()
    tellS w = get >>= \ws -> put $! (ws <> w)

    runListen :: Writer w :< effs' => Eff (Writer w ': effs') b -> Eff effs' (w, b)
    runListen = swizzle
      >>> handle \case
            Tell w -> liftH do
              tellS w
              lift1 $ tell w
            Listen m -> locally $ runListen m
            Censor f m -> locally $ runCensor f m
      >>> runState mempty

    runCensor :: Writer w :< effs' => (w -> w) -> Eff (Writer w ': effs') b -> Eff effs' b
    runCensor f = handle \case
      Tell w -> liftH $ lift1 (tell $! f w)
      Listen m -> locally $ runListen m
      Censor g m -> locally $ runCensor g m

evalWriter :: Monoid w => Eff (Writer w ': effs) a -> Eff effs a
evalWriter = fmap snd . runWriter

execWriter :: Monoid w => Eff (Writer w ': effs) a -> Eff effs w
execWriter = fmap fst . runWriter

runNonDetAll :: Alternative f => Eff (NonDet ': effs) a -> Eff effs (f a)
runNonDetAll = fmap pure >>> handle \case
  Empty -> abort empty
  Choose -> shift \k -> liftA2 (<|>) (k True) (k False)

data Coroutine a b :: Effect where
  Yield :: a -> Coroutine a b m b

yield :: Coroutine a b :< effs => a -> Eff effs b
yield = send . Yield

data Status effs a b c
  = Done c
  | Yielded a !(b -> Eff effs (Status effs a b c))

runCoroutine :: Eff (Coroutine a b ': effs) c -> Eff effs (Status effs a b c)
runCoroutine = fmap Done >>> handle \case
  Yield a -> shift \k -> pure $! Yielded a k
