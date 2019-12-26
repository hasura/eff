{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Effect.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Natural (type (~>))
import Data.Bool
import Data.Kind (Constraint, Type)

import Control.Handler.Internal

#ifdef __HADDOCK_VERSION__
import {-# SOURCE #-} Control.Effect.Error
#endif

-- | The kind of effects, which are classes of monads.
type EffectK = (Type -> Type) -> Constraint

-- | A “monad transformer transformer” for handling effects. Wrapping a monad transformer with
-- 'EffT' allows other effects to be automatically lifted through it by automatically choosing
-- between an effect instance defined on the transformer or an effect instance defined on 'LiftT'
-- depending on whether or not the transformer can handle the given effect, as determined by the
-- 'Handles' type family.
--
-- When defining new effects or handlers, the following instances must be defined to cooperate with
-- 'EffT'’s effect lifting machinery:
--
--   * Effect classes must provide an instance for 'LiftT' that define how the effect ought to be
--     lifted through handlers, and they must also provide an instance for 'EffT' using 'Send' to
--     defer to the appropriate instance.
--
--   * Handler monad transformers must provide an instance of the 'Handles' type family to specify
--     which effects they do and do not handle.
--
-- The other details of delegating to the appropriate handler for each effect are handled
-- automatically.
newtype EffT (t :: HandlerK) m a = EffT { runEffT :: t m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance (Send Alternative t m, Monad (t m)) => Alternative (EffT t m) where
  empty = send @Alternative $ empty
  {-# INLINE empty #-}
  a <|> b = send @Alternative (pure False <|> pure True) >>= bool a b
  {-# INLINABLE (<|>) #-}

instance (Send Alternative t m, Monad (t m)) => MonadPlus (EffT t m)

instance (MonadIO m, MonadTrans t, Monad (t m)) => MonadIO (EffT t m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (MonadBase b m, MonadTrans t, Monad (t m)) => MonadBase b (EffT t m) where
  liftBase = lift . liftBase
  {-# INLINE liftBase #-}

-- | A type alias for a stack of nested 'EffT' transformers: @'EffsT' '[t1, t2, ..., tn] m@ is
-- equivalent to @'EffT' t1 ('EffT' t2 (... ('EffT' tn m) ...))@.
--
-- This can be considered the implementation dual to the 'Can' interface.
type family EffsT ts m where
  EffsT '[]       m = m
  EffsT (t ': ts) m = EffT t (EffsT ts m)

newtype RestrictT (effs :: [EffectK]) (t :: HandlerK) m a = RestrictT { runRestrictT :: t m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)
type instance Handles (RestrictT effs t) eff = eff `Elem` effs

type ScopedT effs m a
  =  forall t. (Handler t, Can effs (t m))
  => EffT (RestrictT effs t) m a

runScopedT :: forall effs t m a. (Handler t, Can effs (t m)) => ScopedT effs m a -> t m a
runScopedT = runRestrictT . runEffT

class Handle (handles :: Bool) (t :: HandlerK) m where
  type HandleTarget handles t m :: Type -> Type
  handle :: HandleTarget handles t m ~> t m
instance Select (IsSpecial t) t m => Handle 'True t m where
  type HandleTarget 'True t m = SelectTarget (IsSpecial t) t m
  handle = select @(IsSpecial t)
  {-# INLINE handle #-}
instance (MonadTrans t, Monad m) => Handle 'False t m where
  type HandleTarget 'False t m = m
  handle = lift
  {-# INLINE handle #-}

type family IsSpecial t where
  IsSpecial (RestrictT _ _) = 'True
  IsSpecial _               = 'False

class Select (special :: Bool) (t :: HandlerK) m where
  type SelectTarget special t m :: Type -> Type
  select :: SelectTarget special t m ~> t m
instance Select 'False t m where
  type SelectTarget 'False t m = t m
  select = id
  {-# INLINE select #-}
instance Select 'True (RestrictT effs t) m where
  type SelectTarget 'True (RestrictT effs t) m = t m
  select = RestrictT
  {-# INLINE select #-}

-- | A typeclass used to lift effectful actions into effect handlers. This is not necessary to use
-- directly when using effects, but it is used as part of defining new effects. Every effect should
-- be given an instance on 'EffT' of the shape
--
-- @
-- instance 'Send' /eff/ t m => /eff/ ('EffT' t m) where
-- @
--
-- where @/eff/@ is replaced by the actual effect in question. Each method should be implemented
-- using 'send' (in a purely mechanical way), which defines the method in terms of 'EffT'’s
-- automatic lifting machinery.
--
-- There is no need to define any additional instances of this class.
class (Handler t, Monad m, eff (Target eff t m)) => Send eff t m where
  type Target eff t m :: Type -> Type

  -- | Lifts an effect operation into 'EffT' using 'EffT'’s automatic lifting machinery. Each
  -- method in the 'EffT' instance for a given effect should use 'send' to defer to an instance on
  -- the appropriate handler.
  --
  -- Each method defined using 'send' should have roughly the following shape:
  --
  -- @
  -- /method/ /a/ /b/ /c/ = 'send' \@/eff/ '$' /method/ /a/ /b/ /c/
  -- @
  --
  -- where @/method/ /a/ /b/ /c/@ should be replaced with the method and its arguments, and @/eff/@
  -- should be replaced with the type of the effect. The explicit type application is necessary
  -- because @eff@ only appears in a constraint in the type signature for 'send', which GHC cannot
  -- automatically infer.
  --
  -- For first-order effects, where @m@ does not appear anywhere in the types of the method
  -- arguments, the above shape is sufficient, and the arguments can be passed to /method/ as-is.
  -- However, for higher-order effects, uses of 'coerce' must be inserted as necessary to safely
  -- coerce the method arguments into the underlying monad. For example, the 'Error' instance for
  -- 'EffT' looks like the following:
  --
  -- @
  -- instance 'Send' ('Error' e) t m => 'Error' e ('EffT' t m) where
  --   'throw' e = 'send' @('Error' e) '$' 'throw' e
  --   'catch' m f = 'send' @('Error' e) '$' 'catch' ('coerce' m) ('coerce' . f)
  -- @
  --
  -- __Note__: it is extremely important to /not/ use 'coerce' around the method result, only around
  -- its arguments. For example, the following definition of 'catch' would typecheck, but it is
  -- incorrect:
  --
  -- @
  -- 'catch' m f = 'send' @('Error' e) '$' 'coerce' ('catch' m f)
  -- @
  --
  -- The problem with the above definition is that it is recursive—it is no different from writing
  --
  -- @
  -- 'catch' m f = 'catch' m f
  -- @
  --
  -- which also typechecks, but is an infinite loop. Therefore, be sure to only apply 'coerce' to
  -- the method arguments, not its result.
  send :: Target eff t m ~> EffT t m

instance (Handler t, Monad m, Handle (Handles t eff) t m, eff (Target eff t m)) => Send eff t m where
  type Target eff t m = HandleTarget (Handles t eff) t m
  send m = EffT (handle @(Handles t eff) m)
  {-# INLINE send #-}

type family All (cs :: [k -> Constraint]) (a :: k) :: Constraint where
  All '[]       _ = ()
  All (c ': cs) a = (c a, All cs a)

-- | A helper type for combining effect constraints: @('Can' '[e1, e2, e3, ..., en] m)@ is
-- equivalent to @(e1 m, e2 m, e3 m, ..., en m)@. The constraint @'Can' effs m@ should be read as
-- specifying that the monad @m@ /can/ perform all of the effects in the list @effs@.
class All effs m => Can (effs :: [EffectK]) m
instance All effs m => Can effs m
