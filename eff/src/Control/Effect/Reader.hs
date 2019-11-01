{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Reader
  ( Reader(..)
  -- * Pure @Reader@ handler
  , runReader
  , ReaderT
  ) where

import qualified Control.Monad.Trans.Reader as Trans

import Control.Effect.Internal
import Control.Handler.Internal
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Data.Coerce

-- | @'Reader' r@ is an effect that provides access to a global environment of type @r@.
--
-- Instances should obey the law @f '<$>' 'ask'@ ≡ @'asks' f@ ≡ @'local' f 'ask'@.
class Monad m => Reader r m where
  {-# MINIMAL (ask | asks), local #-}

  -- | Retrieves a value from the environment.
  ask :: m r
  ask = asks id
  {-# INLINE ask #-}

  -- | Applies a function to a value in the environment and returns the result.
  asks :: (r -> a) -> m a
  asks f = f <$> ask
  {-# INLINE asks #-}

  -- | Runs a subcomputation in an environment modified by the given function.
  local :: (r -> r) -> m a -> m a

instance (Handler t, Reader r m) => Reader r (LiftT t m) where
  ask = lift ask
  {-# INLINE ask #-}
  asks = lift . asks
  {-# INLINE asks #-}
  local f = hmap (local f)
  {-# INLINE local #-}

instance Send (Reader r) t m => Reader r (EffT t m) where
  ask = send @(Reader r) ask
  {-# INLINE ask #-}
  asks f = send @(Reader r) $ asks f
  {-# INLINE asks #-}
  local f m = send @(Reader r) $ local f (coerce m)
  {-# INLINE local #-}

instance Monad m => Reader r (ReaderT r m) where
  ask = Trans.ask
  {-# INLINE ask #-}
  asks = Trans.asks
  {-# INLINE asks #-}
  local = Trans.local
  {-# INLINE local #-}

-- | Handles a @'Reader' r@ effect by supplying a value for the environment.
runReader :: r -> EffT (ReaderT r) m a -> m a
runReader r = flip runReaderT r . runEffT
{-# INLINE runReader #-}
