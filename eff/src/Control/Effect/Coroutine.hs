module Control.Effect.Coroutine
  ( Coroutine(..)
  , yield
  , Status(..)
  , runCoroutine
  ) where

import Control.Effect.Base

data Coroutine a b :: Effect where
  Yield :: a -> Coroutine a b m b

yield :: Coroutine a b :< effs => a -> Eff effs b
yield = send . Yield

data Status effs a b c
  = Done c
  | Yielded a !(b -> Eff (Coroutine a b ': effs) c)

runCoroutine :: Eff (Coroutine a b ': effs) c -> Eff effs (Status effs a b c)
runCoroutine = handle (pure . Done) \case
  Yield a -> control0 \k -> pure $! Yielded a k
