module Control.Effect.Coroutine
  ( Coroutine(..)
  , yield
  , Status(..)
  , runCoroutine
  ) where

import Control.Category ((>>>))
import Control.Effect.Base

data Coroutine a b :: Effect where
  Yield :: a -> Coroutine a b m b

yield :: Coroutine a b :< effs => a -> Eff effs b
yield = send . Yield

data Status effs a b c
  = Done c
  | Yielded a !(b -> Eff effs (Status effs a b c))

runCoroutine :: Eff (Coroutine a b ': effs) c -> Eff effs (Status effs a b c)
runCoroutine = fmap Done >>> handle \case
  Yield a -> shift \k -> pure $! Yielded a k
