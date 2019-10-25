module Control.Effect.Writer where
import Data.Kind (Type)
class Writer w (m :: Type -> Type)
