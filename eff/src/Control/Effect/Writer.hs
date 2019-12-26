{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Writer
  ( Writer(..)
  -- * Pure, strict @Writer@ handler
  --
  -- | Note: this handler is strict in the monoidal state to avoid space leaks, but this requires
  -- 'tell' to produce __left-associated__ uses of '<>', which can be catastrophically slow on
  -- certain monoids, most notably @[]@. To avoid pathological performance, use a data structure
  -- that supports efficient appends, such as @Data.Sequence.Seq@, or use 'Data.Semigroup.Dual' to
  -- flip the argument order of '<>' (but beware that this will cause the elements to be accumulated
  -- in reverse order).
  , runWriter
  , evalWriter
  , execWriter
  , WriterT
  ) where

import Control.Effect.Internal
import Control.Effect.State
import Control.Handler.Internal
import Control.Monad.Trans.Class
import Control.Natural (type (~>), (:~>)(..))
import Data.Function
import Data.Proxy
import Data.Reflection

-- | @'Writer' w@ is an effect that allows the accumulation of monoidal values of type @w@.
--
-- Instances should obey the following laws:
--
--   * @'tell' /x/ '*>' 'tell' /y/@ ≡ @'tell' (/x/ '<>' /y/)@
--   * @'listen' ('tell' /x/)@ ≡ @(/x/,) '<$>' 'tell' /x/@
--   * @'censor' /f/ ('tell' /x/)@ ≡ @'tell' (/f/ /x/)@
--   * @('censor' ('const' 'mempty') ('listen' /e/) '>>=' \\(w, a) -> 'tell' w '$>' a)@ ≡ @/e/@
class (Monoid w, Monad m) => Writer w m where
  -- | Appends the given value to the current output.
  tell :: w -> m ()

  -- | Executes the given action and includes its output in the result.
  listen :: ScopedT '[Writer w] m a -> m (w, a)
  listen = liftListen id
  {-# INLINE listen #-}

  -- | Executes the given action and modifies its output by applying the given function.
  censor :: (w -> w) -> ScopedT '[Writer w] m a -> m a
  censor = liftCensor id
  {-# INLINE censor #-}

  liftListen :: Monad n => (m ~> n) -> ScopedT '[Writer w] n a -> n (w, a)
  liftCensor :: Monad n => (m ~> n) -> (w -> w) -> ScopedT '[Writer w] n a -> n a

instance (Monoid w, Send (Writer w) t m) => Writer w (EffT t m) where
  tell w = send @(Writer w) $ tell w
  {-# INLINE tell #-}
  liftListen liftTo = liftListen @w @(Target (Writer w) t m) $ \m -> liftTo $ send @(Writer w) m
  {-# INLINABLE liftListen #-}
  liftCensor liftTo = liftCensor @w @(Target (Writer w) t m) $ \m -> liftTo $ send @(Writer w) m
  {-# INLINABLE liftCensor #-}

data WriterH
-- | This handler is implemented on top of 'StateT' rather than using a @WriterT@ implementation
-- from @transformers@ because both the strict and lazy @WriterT@ transformers leak space, and
-- @"Control.Monad.Trans.Writer.CPS"@ does not expose the @WriterT@ constructor, precluding an
-- efficient implementation of 'Handler'.
type WriterT w = HandlerT WriterH '[StateT w]
type instance Handles (WriterT w) eff = eff == Writer w

data ListenH s
type ListenT s w = HandlerT (ListenH s) '[StateT w]
type instance Handles (ListenT s w) eff = eff == Writer w

data CensorH s w
type CensorT s w = HandlerT (CensorH s w) '[]
type instance Handles (CensorT s w) eff = eff == Writer w

instance (Monoid w, Monad m) => Writer w (WriterT w m) where
  tell w = HandlerT $ modify (<> w)
  {-# INLINABLE tell #-}

  liftListen liftTo m = reify (NT liftTo) $ \(_ :: Proxy s) ->
    runScopedT @'[Writer w] @(ListenT s w) m
      & runHandlerT
      & runState mempty
  {-# INLINABLE liftListen #-}

  liftCensor liftTo f m = reify (NT liftTo, f) $ \(_ :: Proxy s) ->
    runHandlerT $ runScopedT @'[Writer w] @(CensorT s w) m
  {-# INLINABLE liftCensor #-}

instance (Monoid w, Monad m, Writer w n, Reifies s (n :~> m)) => Writer w (ListenT s w m) where
  tell w = HandlerT (modify (<> w)) *> lift (sendTo $$ tell w)
    where sendTo = reflect $ Proxy @s
  {-# INLINABLE tell #-}

  liftListen liftTo = liftListen $ \m -> liftTo $ lift $ sendTo $$ m
    where sendTo = reflect $ Proxy @s
  {-# INLINABLE liftListen #-}
  liftCensor liftTo = liftCensor $ \m -> liftTo $ lift $ sendTo $$ m
    where sendTo = reflect $ Proxy @s
  {-# INLINABLE liftCensor #-}

instance (Monoid w, Monad m, Writer w n, Reifies s (n :~> m, w -> w)) => Writer w (CensorT s w m) where
  tell w = lift $ sendTo $$ tell (f w)
    where (sendTo, f) = reflect $ Proxy @s
  {-# INLINABLE tell #-}

  liftListen liftTo = liftListen $ \m -> liftTo $ lift $ sendTo $$ m
    where (sendTo, _) = reflect $ Proxy @s
  {-# INLINABLE liftListen #-}
  liftCensor liftTo = liftCensor $ \m -> liftTo $ lift $ sendTo $$ m
    where (sendTo, _) = reflect $ Proxy @s
  {-# INLINABLE liftCensor #-}

runWriter :: (Monoid w, Functor m) => EffT (WriterT w) m a -> m (w, a)
runWriter = runState mempty . runHandlerT . runEffT

evalWriter :: (Monoid w, Monad m) => EffT (WriterT w) m a -> m a
evalWriter = evalState mempty . runHandlerT . runEffT

execWriter :: (Monoid w, Monad m) => EffT (WriterT w) m a -> m w
execWriter = execState mempty . runHandlerT . runEffT
