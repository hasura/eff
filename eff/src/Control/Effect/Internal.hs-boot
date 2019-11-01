module Control.Effect.Internal where

import {-# SOURCE #-} Control.Handler.Internal

import Control.Monad.Trans.Class
import Data.Kind (Constraint, Type)

type EffectK = (Type -> Type) -> Constraint

newtype EffT t (m :: Type -> Type) a = EffT { runEffT :: t m a }
instance Functor (t m) => Functor (EffT t m)
instance Applicative (t m) => Applicative (EffT t m)
instance Monad (t m) => Monad (EffT t m)
instance MonadTrans t => MonadTrans (EffT t)
instance Handler t => Handler (EffT t)

type family EffsT ts m where
  EffsT '[]       m = m
  EffsT (t ': ts) m = EffT t (EffsT ts m)
