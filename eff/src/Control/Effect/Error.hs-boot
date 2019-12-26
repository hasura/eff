module Control.Effect.Error where

import Control.Natural (type (~>))

import {-# SOURCE #-} Control.Effect.Internal

class Monad m => Error e m where
  throw :: e -> m a

  catch :: ScopedT '[Error e] m a -> (e -> m a) -> m a
  catch = liftCatch id
  {-# INLINE catch #-}

  liftCatch :: Monad n => (m ~> n) -> ScopedT '[Error e] n a -> (e -> n a) -> n a
