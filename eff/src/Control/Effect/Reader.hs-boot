module Control.Effect.Reader where
import Data.Kind (Type)
class Reader r (m :: Type -> Type)
