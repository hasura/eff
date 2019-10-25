module Control.Effect.Error where
import Data.Kind (Type)
class Error e (m :: Type -> Type)
