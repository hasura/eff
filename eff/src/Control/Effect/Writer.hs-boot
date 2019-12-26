module Control.Effect.Writer where
class (Monoid w, Monad m) => Writer w m where
  tell :: w -> m ()
  listen :: m a -> m (w, a)
  censor :: (w -> w) -> m a -> m a
