module Control.Handler.Internal where

import Control.Monad.Trans.Class
import Data.Functor.Compose
import Data.Kind (Constraint, Type)

type HandlerK = (Type -> Type) -> Type -> Type
type TacticK = HandlerK -> Constraint

class ( MonadTrans t
      , forall m. Functor m => Functor (t m)
      , forall m. Monad m => Monad (t m)
      ) => Handler t where
  hmap :: (Functor m, Functor n) => (forall b. m b -> n b) -> t m a -> t n a

class Handler t => Accumulate t where
  {-# MINIMAL accumulate | hmapS #-}

  accumulate :: Functor m => t (Compose m ((,) s)) a -> t m (s, a)
  accumulate = hmapS getCompose
  {-# INLINE accumulate #-}

  hmapS :: (Functor m, Functor n) => (forall b. m b -> n (s, b)) -> t m a -> t n (s, a)
  hmapS f = accumulate . hmap (Compose . f)
  {-# INLINABLE hmapS #-}

class Handler t => Choice t where
  choice :: (Functor m, Functor n) => (forall b. (t m a -> m b) -> n b) -> t n a

type family Handles (t :: HandlerK) (eff :: (Type -> Type) -> Constraint) :: Bool
