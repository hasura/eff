module Control.Effect.State where

class Monad m => State s m where
  {-# MINIMAL get, (put | modify) #-}
  get :: m s

  put :: s -> m ()
  put = modify . const
  {-# INLINE put #-}

  modify :: (s -> s) -> m ()
  modify f = put . f =<< get
  {-# INLINE modify #-}
