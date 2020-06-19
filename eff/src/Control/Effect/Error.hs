module Control.Effect.Error
  ( Error(..)
  , throw
  , catch
  , runError
  ) where

import Control.Effect.Base

-- | The @'Error' e@ effect allows throwing and catching errors of type @e@.
--
-- Handlers should obey the law @'catch' ('throw' /x/) /f/@ ≡ @'pure' (/f/ /x/)@.
data Error e :: Effect where
  Throw :: e -> Error e m a
  Catch :: Eff (Error e ': effs) a -> (e -> Eff effs a) -> Error e (Eff effs) a

-- | Raises an error of type @e@.
throw :: Error e :< effs => e -> Eff effs a
throw = send . Throw

-- | @'catch' /m/ /f/@ executes @/m/@. If it raises an error @/e/@, the
-- computation aborts to the point of the call to 'catch', and it resumes by
-- executing @/f/ /e/@.
catch :: Error e :< effs => Eff (Error e ': effs) a -> (e -> Eff effs a) -> Eff effs a
catch a b = send $ Catch a b

-- | Handles an 'Error' effect. Returns 'Left' if the computation raised an
-- uncaught error, otherwise returns 'Right'.
runError :: forall e a effs. Eff (Error e ': effs) a -> Eff effs (Either e a)
runError = handle (pure . Right) \case
  Throw e -> abort $ Left e
  Catch m f -> locally (either f pure =<< runError m)
