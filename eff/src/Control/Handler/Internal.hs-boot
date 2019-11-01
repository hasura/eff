module Control.Handler.Internal where

import Data.Kind (Type)

type HandlerK = (Type -> Type) -> Type -> Type
class Handler (t :: HandlerK)
