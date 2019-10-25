module Control.Handler.Internal where

import Control.Monad.Trans.Class
import Data.Kind (Constraint, Type)

type HandlerK = (Type -> Type) -> Type -> Type

class (MonadTrans t, forall m. Monad m => Monad (t m), Functor (HandlerState t)) => Handler t where
  type HandlerState t :: Type -> Type
  liftWith
    :: Monad m
    => ((forall r. t m r -> m (HandlerState t r)) -> m (HandlerState t a))
    -> t m a

type family Handles (t :: HandlerK) (eff :: (Type -> Type) -> Constraint) :: Bool
