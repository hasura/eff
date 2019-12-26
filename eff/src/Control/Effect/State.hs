{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.State
  ( State(..)
  -- * Pure, strict @State@ handler
  --
  -- | Note: this handler provides 'put' and 'modify' operations that are strict in the state, even
  -- though 'Trans.put' and 'Trans.modify' from "Control.Monad.Trans.State.Strict" are lazy in the
  -- state. If you have a use case for lazy 'put'/'modify' with a strict 'State' handler, let me
  -- know, but in my experience this is what everyone wants, anyway.
  , runState
  , evalState
  , execState
  , StateT
  ) where

import qualified Control.Monad.Trans.State.Strict as Trans

import Control.Effect.Internal
import Control.Monad.Trans.State.Strict (StateT, execStateT, evalStateT, runStateT)
import Data.Tuple

-- | @'State' s@ is an effect that provides access to a single cell of mutable state of type @s@.
class Monad m => State s m where
  {-# MINIMAL get, (put | modify) #-}

  -- | Retrieves the current value of the state.
  get :: m s

  -- | Replaces the current state with the given value.
  put :: s -> m ()
  put = modify . const
  {-# INLINE put #-}

  -- | Modifies the current state by applying the given function to it.
  modify :: (s -> s) -> m ()
  modify f = put . f =<< get
  {-# INLINE modify #-}

instance Send (State s) t m => State s (EffT t m) where
  get = send @(State s) get
  {-# INLINE get #-}
  put s = send @(State s) $ put s
  {-# INLINE put #-}
  modify f = send @(State s) $ modify f
  {-# INLINE modify #-}

-- | Note: this instance provides 'put' and 'modify' operations that are strict in the state.
instance Monad m => State s (StateT s m) where
  get = Trans.get
  {-# INLINE get #-}
  put !s = Trans.put s
  {-# INLINE put #-}
  modify = Trans.modify'
  {-# INLINE modify #-}

runState :: forall s m a. Functor m => s -> EffT (StateT s) m a -> m (s, a)
runState s = fmap swap . flip runStateT s . runEffT
{-# INLINE runState #-}

evalState :: forall s m a. Monad m => s -> EffT (StateT s) m a -> m a
evalState s = flip evalStateT s . runEffT
{-# INLINE evalState #-}

execState :: forall s m a. Monad m => s -> EffT (StateT s) m a -> m s
execState s = flip execStateT s . runEffT
{-# INLINE execState #-}
