{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Effect.Internal where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..))
import Control.Monad.Base (MonadBase(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Kind (Constraint, Type)

import {-# SOURCE #-} Control.Handler.Internal

-- | The kind of effects, which are classes of monads.
type EffectK = (Type -> Type) -> Constraint

-- | A monad transformer for handling effects. @('EffT' t)@ is actually no different from @t@ at
-- runtime, but it provides a different set of instances. Wrapping a monad transformer with 'EffT'
-- allows other effects to be automatically lifted through it, provided the underlying transformer
-- provides a 'Handler' instance.
--
-- 'EffT' cannot be used with any arbitrary monad transformer: all monad transformers wrapped with
-- 'EffT' /must/ provide an instance of the 'Handles' type family to cooperate with effect with the
-- effect lifting machinery. However, note that this requirement only applies to transformers
-- wrapped in 'EffT' directly, i.e. used as the @t@ argument in @('EffT' t)@; there are no
-- restrictions placed on the underlying monad (though effects will not be able to be automatically
-- lifted through non-'EffT' layers).
newtype EffT (t :: HandlerK) m a = EffT { runEffT :: t m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans, Handler)

instance (Send Alternative t m, Monad (t m)) => Alternative (EffT t m) where
  empty = send @Alternative empty
  {-# INLINE empty #-}
  a <|> b = sendWith @Alternative
    (runEffT a <|> runEffT b)
    (liftWith $ \lower -> lower (runEffT a) <|> lower (runEffT b))
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

class Handle (handles :: Bool) eff t m where
  handle
    :: (eff (t m) => t m a)
    -> ((Handler t, eff m) => t m a)
    -> EffT t m a

instance eff (t m) => Handle 'True eff t m where
  handle m _ = EffT m
  {-# INLINE handle #-}

instance (Handler t, eff m) => Handle 'False eff t m where
  handle _ m = EffT m
  {-# INLINE handle #-}

-- | A typeclass used to lift effectful actions into effect handlers. This is not necessary to use
-- directly when using effects, but it is used as part of defining new effects. Every effect should
-- be given an instance on 'EffT' of the shape
--
-- @
-- instance 'Send' /eff/ t m => /eff/ ('EffT' t m) where
-- @
--
-- where @/eff/@ is replaced by the actual effect in question. Each method should be implemented
-- using 'send' or 'sendWith': 'send' for algebraic/first-order operations and 'sendWith' for
-- scoped/higher-order ones.
--
-- There is no need to define any additional instances of this class.
class (Monad m, Handle (Handles t eff) eff t m) => Send eff t m where
  -- | Constructs an @'EffT' t m a@ computation for an algebraic/first-order operation. Each
  -- first-order method in the 'EffT' instance for a given effect should have the shape
  --
  -- @
  -- /method/ /a/ /b/ /c/ = 'send' \@/eff/ (/method/ /a/ /b/ /c/)
  -- @
  --
  -- where @/method/ /a/ /b/ /c/@ should be replaced with the method and its arguments, and @/eff/@
  -- should be replaced with the type of the effect. The explicit type application is necessary
  -- because @eff@ only appears in a constraint in the type signature for 'send', which GHC cannot
  -- automatically infer.
  --
  -- @'send' \@/eff/ /m/@ is equivalent to @'sendWith' \@/eff/ /m/ ('lift' /m/)@.
  send :: (forall n. eff n => n a) -> EffT t m a
  send m = sendWith @eff m (lift m)
  {-# INLINE send #-}

  -- | Constructs an @'EffT' t m a@ computation for a higher-order/scoped effect @eff@ from two
  -- actions:
  --
  --   1. A “run” action, which executes the effect in the @(t m)@ monad given @(t m)@ has an
  --      instance of @eff@.
  --
  --   2. A “lift” action, which lifts the effect through @(t m)@ into @m@ given that @t@ has a
  --      'Handler' instance and @m@ has an instance of @eff@.
  --
  -- Each higher-order method in the 'EffT' instance for a given effect should use 'sendWith' to
  -- specify how it ought to be lifted through effect handlers. For example, the definition of
  -- 'Control.Effect.Reader.local' looks like this:
  --
  -- @
  -- 'Control.Effect.Reader.local' f m = 'sendWith' @('Control.Effect.Reader.Reader' r)
  --   ('Control.Effect.Reader.local' f ('runEffT' m))
  --   ('liftWith' '$' \\lower -> 'Control.Effect.Reader.local' f (lower '$' 'runEffT' m))
  -- @
  --
  -- With this instance in place, @'Control.Effect.Reader.Reader' r@ can automatically be used with
  -- @'EffT' t m a@. Transformers that can handle the @'Control.Effect.Reader.Reader' r@ effect
  -- (i.e. ones for which @'Handles' t ('Control.Effect.Reader.Reader' r) ~ ''True'@) will use their
  -- @'Control.Effect.Reader.Reader' r@ instances, while other transformers will delegate to the
  -- underlying monad.
  sendWith
    :: (eff (t m) => t m a)
    -- ^ An action to run in the current handler.
    -> ((Handler t, eff m) => t m a)
    -- ^ An action that delegates to the underlying monad.
    -> EffT t m a

instance (Monad m, Handle (Handles t eff) eff t m) => Send eff t m where
  sendWith = handle @(Handles t eff) @eff
  {-# INLINE sendWith #-}

type family All (cs :: [k -> Constraint]) (a :: k) :: Constraint where
  All '[]       _ = ()
  All (c ': cs) a = (c a, All cs a)

-- | A helper type for combining effect constraints: @('Can' '[e1, e2, e3, ..., en] m)@ is
-- equivalent to @(e1 m, e2 m, e3 m, ..., en m)@. The constraint @'Can' effs m@ should be read as
-- specifying that the monad @m@ /can/ perform all of the effects in the list @effs@.
class All effs m => Can (effs :: [EffectK]) m
instance All effs m => Can effs m
