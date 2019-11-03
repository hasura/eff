module Control.Effect.Error where
class Monad m => Error e m where
  throw :: e -> m a
  catch :: m a -> (e -> m a) -> m a
