{-# LANGUAGE PolyKinds #-}

module Control.Handler.Internal where

import Data.Kind (Type)

type HandlerK = (Type -> Type) -> Type -> Type
class Handler (t :: HandlerK)

type role HandlerT phantom nominal nominal nominal
data HandlerT tag (ts :: [HandlerK]) :: HandlerK
