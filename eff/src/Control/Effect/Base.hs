{-# OPTIONS_HADDOCK not-home #-}

-- | This module exports the core functionality @eff@ without any of the
-- built-in effects or effect handlers. You can import this module if you don’t
-- want to import the built-in effects, but otherwise you probably want to
-- import "Control.Effect" instead.
module Control.Effect.Base (
  -- * The @Eff@ monad
    Eff
  , run
  , lift
  , lift1

  -- * Defining new effects
  , Effect
  , send
  , (:<)
  , (:<<)

  -- * Handling effects
  -- ** Simple effect handlers
  , interpret
  -- ** Advanced effect handlers
  , Handle
  , handle
  , liftH
  , abort
  , control
  , control0
  , locally

  -- * Performing I/O
  , IOE(..)
  , MonadIO(..)
  , runIO
  ) where

import Control.Monad.IO.Class

import Control.Effect.Internal

-- | The simplest way to handle an effect. Each use of 'send' for the handled
-- effect dispatches to the handler function, which provides an interpretation
-- for the operation. The handler function may handle the operation directly, or
-- it may defer to other effects currently in scope.
--
-- Most effect handlers should be implemented using 'interpret', possibly with
-- the help of additional 'Control.Effect.Error.Error' or 'State' effects.
-- Especially complex handlers can be defined via the more general 'handle',
-- which 'interpret' is defined in terms of:
--
-- @
-- 'interpret' f = 'handle' ('liftH' '.' f)
-- @
interpret
  :: forall eff a effs
   . (forall m b. eff m b -> Eff (eff ': effs) b)
  -- ^ The handler function.
  -> Eff (eff ': effs) a
  -- ^ The action to handle.
  -> Eff effs a
interpret f = handle pure (liftH . f)
