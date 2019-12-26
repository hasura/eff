module Control.Effect.Reader where

import Control.Natural (type (~>))

import {-# SOURCE #-} Control.Effect.Internal

class Monad m => Reader r m where
  {-# MINIMAL (ask | asks), liftLocal #-}

  ask :: m r
  ask = asks id
  {-# INLINE ask #-}

  asks :: (r -> a) -> m a
  asks f = f <$> ask
  {-# INLINE asks #-}

  local :: (r -> r) -> ScopedT '[Reader r] m a -> m a
  local = liftLocal id
  {-# INLINE local #-}

  liftLocal :: Monad n => (m ~> n) -> (r -> r) -> ScopedT '[Reader r] n a -> n a
