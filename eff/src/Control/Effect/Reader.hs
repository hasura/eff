{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Reader
  ( Reader(..)
  -- * Pure @Reader@ handler
  , runReader
  , ReaderT
  ) where

import qualified Control.Monad.Trans.Reader as Trans

import Control.Effect.Internal
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Control.Natural (type (~>))

-- | @'Reader' r@ is an effect that provides access to a global environment of type @r@.
--
-- Instances should obey the law @f '<$>' 'ask'@ ≡ @'asks' f@ ≡ @'local' f 'ask'@.
class Monad m => Reader r m where
  {-# MINIMAL (ask | asks), liftLocal #-}

  -- | Retrieves a value from the environment.
  ask :: m r
  ask = asks id
  {-# INLINE ask #-}

  -- | Applies a function to a value in the environment and returns the result.
  asks :: (r -> a) -> m a
  asks f = f <$> ask
  {-# INLINE asks #-}

  -- | Runs a subcomputation in an environment modified by the given function.
  local :: (r -> r) -> ScopedT '[Reader r] m a -> m a
  local = liftLocal id
  {-# INLINE local #-}

  liftLocal :: Monad n => (m ~> n) -> (r -> r) -> ScopedT '[Reader r] n a -> n a

instance Send (Reader r) t m => Reader r (EffT t m) where
  ask = send @(Reader r) ask
  {-# INLINE ask #-}
  asks f = send @(Reader r) $ asks f
  {-# INLINE asks #-}
  liftLocal liftTo = liftLocal @r @(Target (Reader r) t m) $ \m -> liftTo $ send @(Reader r) m
  {-# INLINABLE liftLocal #-}

instance Monad m => Reader r (ReaderT r m) where
  ask = Trans.ask
  {-# INLINE ask #-}
  asks = Trans.asks
  {-# INLINE asks #-}
  liftLocal liftTo f m = do
    r <- liftTo Trans.ask
    runReader (f r) (runScopedT @'[Reader r] m)
  {-# INLINABLE liftLocal #-}

-- | Handles a @'Reader' r@ effect by supplying a value for the environment.
runReader :: r -> EffT (ReaderT r) m a -> m a
runReader r = flip runReaderT r . runEffT
{-# INLINE runReader #-}
