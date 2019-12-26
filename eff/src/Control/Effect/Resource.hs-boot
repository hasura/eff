module Control.Effect.Resource where
class Monad m => Mask m where
  mask :: ((forall a. m a -> m a) -> m b) -> m b
  uninterruptibleMask :: ((forall a. m a -> m a) -> m b) -> m b
