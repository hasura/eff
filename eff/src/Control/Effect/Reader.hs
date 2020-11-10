module Control.Effect.Reader
  ( Reader(..)
  , ask
  , local
  , runReader
  ) where

import Control.Effect.Base

-- | The @'Reader' r@ effect provides access to a global environment of type @r@.
--
-- Handlers should obey the law @/f/ '<$>' 'ask'@ ≡ @'local' /f/ 'ask'@.
data Reader r :: Effect where
  Ask :: Reader r m r
  Local :: (r1 -> r2) -> Eff (Reader r2 ': effs) a -> Reader r1 (Eff effs) a

-- | Retrieves a value from the environment.
ask :: Reader r :< effs => Eff effs r
ask = send Ask

-- | Runs a subcomputation in an environment modified by the given function.
local :: Reader r1 :< effs => (r1 -> r2) -> Eff (Reader r2 ': effs) a -> Eff effs a
local a b = send $ Local a b

-- | Handles a @'Reader'@ effect by supplying a value for the environment.
runReader :: r -> Eff (Reader r ': effs) a -> Eff effs a
runReader r = handle pure \case
  Ask -> liftH $ pure r
  Local f m -> locally let !r' = f r in runReader r' m
