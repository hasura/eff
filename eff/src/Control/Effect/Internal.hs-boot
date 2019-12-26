module Control.Effect.Internal where

import Control.Monad.Trans.Class
import Data.Kind (Constraint, Type)

import {-# SOURCE #-} Control.Handler.Internal

type EffectK = (Type -> Type) -> Constraint

newtype EffT (t :: HandlerK) m a = EffT { runEffT :: t m a }
instance Functor (t m) => Functor (EffT t m)
instance Applicative (t m) => Applicative (EffT t m)
instance Monad (t m) => Monad (EffT t m)
instance MonadTrans t => MonadTrans (EffT t)

type family EffsT ts m where
  EffsT '[]       m = m
  EffsT (t ': ts) m = EffT t (EffsT ts m)

newtype RestrictT (effs :: [EffectK]) (t :: HandlerK) m a = RestrictT { runRestrictT :: t m a }

type ScopedT effs m a
  =  forall t. (Handler t, Can effs (t m))
  => EffT (RestrictT effs t) m a

class Can (effs :: [EffectK]) (m :: Type -> Type)
