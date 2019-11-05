module Control.Effect.Reader where
class Monad m => Reader r m where
  {-# MINIMAL (ask | asks), local #-}

  ask :: m r
  ask = asks id
  {-# INLINE ask #-}

  asks :: (r -> a) -> m a
  asks f = f <$> ask
  {-# INLINE asks #-}

  local :: (r -> r) -> m a -> m a
