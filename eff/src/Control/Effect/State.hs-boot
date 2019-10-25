module Control.Effect.State where
import Data.Kind (Type)
class State s (m :: Type -> Type)
