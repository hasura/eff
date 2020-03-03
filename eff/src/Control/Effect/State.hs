module Control.Effect.State
  ( State(..)
  , get
  , put
  , modify
  ) where

import Control.Effect.Base
import Control.Effect.Internal (State(..))

-- | Retrieves the current value of the state.
get :: State s :< effs => Eff effs s
get = send Get

-- | Replaces the current state with the given value.
put :: State s :< effs => s -> Eff effs ()
put = send . Put

-- | Modifies the current state by applying the given function to it.
modify :: State s :< effs => (s -> s) -> Eff effs ()
modify f = get >>= put . f
