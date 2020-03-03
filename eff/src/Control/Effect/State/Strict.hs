module Control.Effect.State.Strict
  ( module Control.Effect.State
  , runState
  , evalState
  , execState
  ) where

import Control.Effect.Base
import Control.Effect.State
import Control.Effect.Internal (evalState)
import Data.Tuple (swap)

-- | Handles a @'State'@ effect using a strict cell of mutable state—each use
-- of 'put' or 'modify' eagerly forces the new value. The state is initialized
-- to the given value, and the final state is returned alongside the
-- computation’s result.
runState :: s -> Eff (State s ': effs) a -> Eff effs (s, a)
runState s m = evalState s (curry swap <$> m <*> get)

execState :: s -> Eff (State s ': effs) a -> Eff effs s
execState s m = evalState s (m *> get)
