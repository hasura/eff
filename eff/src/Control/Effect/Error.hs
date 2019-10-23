{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Error
  ( Error(..)
  -- * Pure @Error@ handler
  --
  -- | For historical reasons, the canonical handler for the 'Error' effect provided by
  -- @transformers@ has the name 'ExceptT', not @ErrorT@. To avoid confusion, this library does not
  -- export it under a different alias. However, the handler function is still named 'runError'.
  , runError
  , ExceptT
  ) where

import qualified Control.Monad.Trans.Except as Trans

import Control.Effect.Internal
import Control.Monad.Trans.Except (ExceptT, runExceptT)

-- | @'Error' e@ is an effect that allows throwing and catching errors of type @e@. Note that these
-- have no relation to Haskell’s built-in support for synchronous or asynchronous runtime exceptions
-- provided from "Control.Exception".
--
-- Instances should obey the law @'catch' ('throw' x) f@ ≡ @'pure' (f x)@.
class Monad m => Error e m where
  -- | Raises an error of type @e@.
  throw :: e -> m a
  -- | Runs the given sub-computation. If it raises an error of type @e@, the error is provided to
  -- the given handler function, and execution resumes from the point of the call to 'catch'.
  catch :: m a -> (e -> m a) -> m a

instance (Monad (t m), Send (Error e) t m) => Error e (EffT t m) where
  throw e = send @(Error e) (throw e)
  {-# INLINE throw #-}
  catch m f = sendWith @(Error e)
    (catch (runEffT m) (runEffT . f))
    (controlT $ \run -> catch (run $ runEffT m) (run . runEffT . f))
  {-# INLINABLE catch #-}

instance Monad m => Error e (ExceptT e m) where
  throw = Trans.throwE
  {-# INLINE throw #-}
  catch = Trans.catchE
  {-# INLINE catch #-}

-- | Handles an @'Error' e@ effect. Returns 'Left' if the computation raised an uncaught error,
-- otherwise returns 'Right'.
runError :: EffT (ExceptT e) m a -> m (Either e a)
runError = runExceptT . runEffT
{-# INLINE runError #-}
