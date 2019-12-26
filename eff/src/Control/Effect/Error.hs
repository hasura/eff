{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE UndecidableSuperClasses #-}

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

import Control.Effect.Internal
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Natural (type (~>))

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
  catch :: ScopedT '[Error e] m a -> (e -> m a) -> m a
  catch = liftCatch id
  {-# INLINE catch #-}

  liftCatch :: Monad n => (m ~> n) -> ScopedT '[Error e] n a -> (e -> n a) -> n a

instance Send (Error e) t m => Error e (EffT t m) where
  throw e = send @(Error e) $ throw e
  {-# INLINE throw #-}
  liftCatch liftTo = liftCatch @e @(Target (Error e) t m) $ \m -> liftTo $ send @(Error e) m
  {-# INLINABLE liftCatch #-}

instance Monad m => Error e (ExceptT e m) where
  throw = throwE
  {-# INLINE throw #-}
  liftCatch _ m f = runError (runScopedT @'[Error e] m) >>= either f pure
  {-# INLINABLE liftCatch #-}

-- | Handles an @'Error' e@ effect. Returns 'Left' if the computation raised an uncaught error,
-- otherwise returns 'Right'.
runError :: EffT (ExceptT e) m a -> m (Either e a)
runError = runExceptT . runEffT
{-# INLINE runError #-}
