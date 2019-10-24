{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Effect.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.Base (MonadBase(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Control
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.State.Strict (StateT)
import Data.Kind (Constraint, Type)
import Data.Proxy

import {-# SOURCE #-} Control.Effect.Error
import {-# SOURCE #-} Control.Effect.Reader
import {-# SOURCE #-} Control.Effect.State

-- | The kind of effect handlers, which are monad transformers.
type HandlerK = (Type -> Type) -> Type -> Type
-- | The kind of effects, which are classes of monads.
type EffectK = (Type -> Type) -> Constraint

-- | A monad transformer for handling effects. @('EffT' t)@ is actually no different from @t@ at
-- runtime, but it provides a different set of instances. Wrapping a monad transformer with 'EffT'
-- allows other effects to be automatically lifted through it, provided the underlying transformer
-- provides a 'MonadTransControl' instance.
--
-- 'EffT' cannot be used with any arbitrary monad transformer: all monad transformers wrapped with
-- 'EffT' /must/ provide an instance of the 'Handles' type family to cooperate with effect with the
-- effect lifting machinery. However, note that this requirement only applies to transformers
-- wrapped in 'EffT' directly, i.e. used as the @t@ argument in @('EffT' t)@; there are no
-- restrictions placed on the underlying monad (though effects will not be able to be automatically
-- lifted through non-'EffT' layers).
newtype EffT (t :: HandlerK) m a = EffT { runEffT :: t m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans, MonadTransControl)

instance (Send Alternative t m, Monad (t m)) => Alternative (EffT t m) where
  empty = send @Alternative empty
  {-# INLINE empty #-}
  a <|> b = sendWith @Alternative
    (runEffT a <|> runEffT b)
    (controlT $ \lower -> lower (runEffT a) <|> lower (runEffT b))
  {-# INLINABLE (<|>) #-}

instance (Send Alternative t m, Monad (t m)) => MonadPlus (EffT t m)

instance (MonadIO m, MonadTrans t, Monad (t m)) => MonadIO (EffT t m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (MonadBase b m, MonadTrans t, Monad (t m)) => MonadBase b (EffT t m) where
  liftBase = lift . liftBase
  {-# INLINE liftBase #-}

instance (MonadBaseControl b m, MonadTransControl t, Monad (t m)) => MonadBaseControl b (EffT t m) where
  type StM (EffT t m) a = ComposeSt (EffT t) m a
  liftBaseWith = defaultLiftBaseWith
  {-# INLINE liftBaseWith #-}
  restoreM = defaultRestoreM
  {-# INLINE restoreM #-}

-- | A type alias for a stack of nested 'EffT' transformers: @'EffsT' '[t1, t2, ..., tn] m@ is
-- equivalent to @'EffT' t1 ('EffT' t2 (... ('EffT' tn m) ...))@.
--
-- This can be considered the implementation dual to the 'Can' interface.
type family EffsT ts m where
  EffsT '[]       m = m
  EffsT (t ': ts) m = EffT t (EffsT ts m)

-- | An __internal__ helper class used to work around GHC’s inability to handle quantified
-- constraints over type families. The constraint @(forall m. c m => 'OverEffs' c ts m)@ is morally
-- equivalent to @(forall m. c m => c (EffsT ts m))@, but the latter is not allowed by GHC. The cost
-- of this less direct encoding is that instances must be manually brought into scope using
-- 'overEffs' and visible type application.
class OverEffs c ts m where
  overEffs :: (c (EffsT ts m) => r) -> r
instance c (EffsT ts m) => OverEffs c ts m where
  overEffs = id
  {-# INLINE overEffs #-}

-- | An __internal__ helper class used to implement 'MonadTrans' and 'MonadTransControl' instances
-- for 'HandlerT'. This allows us to avoid making 'HandlerT' a data family by using 'inductHandler'
-- to perform induction over the type-level list of handlers. (We want to avoid making 'HandlerT' a
-- data family so that the interface is simpler, as it allows 'runHandlerT' to return an ordinary
-- stack of 'EffT' transformers.)
class InductHandler c tag ts where
  inductHandler
    :: (ts ~ '[] => r)
    -> (forall t ts'.
         ( ts ~ (t ': ts')
         , c t
         , c (HandlerT tag ts')
         , forall m. Monad m => OverEffs Monad ts' m
         )
       => Proxy ts -> r)
    -> r
instance InductHandler c tag '[] where
  inductHandler a _ = a
  {-# INLINE inductHandler #-}
instance
  ( forall m. Monad m => OverEffs Monad ts m
  , c t, c (HandlerT tag ts)
  ) => InductHandler c tag (t ': ts) where
  inductHandler _ b = b (Proxy @(t ': ts))
  {-# INLINE inductHandler #-}

-- | A helper for defining effect handlers in terms of other, existing handlers. @('HandlerT' tag
-- ts)@ is equivalent to @('EffsT' ts)@, but the phantom @tag@ parameter is useful as a way to
-- disambiguate between different handler instances.
newtype HandlerT tag ts m a = HandlerT { runHandlerT :: EffsT ts m a }
deriving newtype instance Functor (EffsT ts m) => Functor (HandlerT tag ts m)
deriving newtype instance Applicative (EffsT ts m) => Applicative (HandlerT tag ts m)
deriving newtype instance Alternative (EffsT ts m) => Alternative (HandlerT tag ts m)
deriving newtype instance Monad (EffsT ts m) => Monad (HandlerT tag ts m)
deriving newtype instance MonadPlus (EffsT ts m) => MonadPlus (HandlerT tag ts m)
deriving newtype instance MonadIO (EffsT ts m) => MonadIO (HandlerT tag ts m)
deriving newtype instance (Monad b, MonadBase b (EffsT ts m)) => MonadBase b (HandlerT tag ts m)
deriving newtype instance (Monad b, MonadBaseControl b (EffsT ts m)) => MonadBaseControl b (HandlerT tag ts m)

instance InductHandler MonadTrans tag ts => MonadTrans (HandlerT tag ts) where
  lift :: forall m a. Monad m => m a -> HandlerT tag ts m a
  lift = inductHandler @MonadTrans @tag @ts HandlerT $
    \(_ :: Proxy (t ': ts')) -> overEffs @Monad @ts' @m $
      HandlerT . lift . runHandlerT . lift @(HandlerT tag ts')
  {-# INLINABLE lift #-}

type family StEffsT ts a where
  StEffsT '[]       a = a
  StEffsT (t ': ts) a = StEffsT ts (StT (EffT t) a)

instance
  ( MonadTrans (HandlerT tag ts), InductHandler MonadTransControl tag ts
  ) => MonadTransControl (HandlerT tag ts) where
  type StT (HandlerT tag ts) a = StEffsT ts a

  liftWith :: forall m a. Monad m => (Run (HandlerT tag ts) -> m a) -> HandlerT tag ts m a
  liftWith f = inductHandler @MonadTransControl @tag @ts
    (HandlerT $ f runHandlerT)
    (\(_ :: Proxy (t ': ts')) -> overEffs @Monad @ts' @m $
      HandlerT $ liftWith $ \lowerT ->
        runHandlerT $ liftWith @(HandlerT tag ts') @m $ \lowerTs ->
          let lower :: forall n b. Monad n => HandlerT tag ts n b -> n (StEffsT ts' (StT t b))
              lower m = overEffs @Monad @ts' @n $
                lowerTs $ HandlerT $ lowerT $ runHandlerT m
          in f lower)
  {-# INLINABLE liftWith #-}

  restoreT :: forall m a. Monad m => m (StEffsT ts a) -> HandlerT tag ts m a
  restoreT m = inductHandler @MonadTransControl @tag @ts
    (HandlerT m)
    (\(_ :: Proxy (t ': ts')) -> overEffs @Monad @ts' @m $
      HandlerT $ restoreT $ runHandlerT $ restoreT @(HandlerT tag ts') m)
  {-# INLINABLE restoreT #-}

-- | An open type family that is used to determine which effects ought to be handled by which
-- handlers. If @'Handles' t eff@ ~ ''True' for some handler @t@ and effect @eff@, the handler will
-- be used to handle any effects sent to it via 'send'; otherwise, the effect will be lifted to the
-- next handler in the stack.
--
-- It is important that @'Handles' t@ is total in its argument; that is, it is important that
-- effects that /cannot/ be handled produce @''False'@, not just that effects that can be handled
-- produce @''True'@. The 'Data.Type.Equality.==' type family is provided for this purpose: If a
-- handler only handles a single effect, its 'Handles' instance should look like the following:
--
-- @
-- type 'Handles' MyEffectT eff = eff 'Data.Type.Equality.==' MyEffect
-- @
--
-- If it handles multiple effects, it can use the 'Elem' type family instead:
--
-- @
-- type 'Handles' MyEffectT eff = eff `'Elem'` '[MyEffect1, MyEffect2]
-- @
--
-- More complex 'Handles' instances are possible, but not generally very useful.
type family Handles (t :: HandlerK) (eff :: EffectK) :: Bool
type instance Handles (ExceptT e) eff = eff == Error e
type instance Handles (ReaderT r) eff = eff == Reader r
type instance Handles (StateT s) eff = eff == State s

-- | Boolean equality on types.
--
-- This is essentially the same as @==@ from "Data.Type.Equality", but the version from
-- "Data.Type.Equality" is written in such a way that allows GHC to deduce more information from
-- @''True'@ results but causes trouble when trying to compute the equality of rigid type variables.
-- This definition uses a simpler version.
type family a == b where
  a == a = 'True
  _ == _ = 'False

-- | Checks if @x@ is in the type-level list @xs@ (like 'elem', but at the type level).
type family Elem (x :: k) (xs :: [k]) :: Bool where
  Elem _ '[]       = 'False
  Elem x (x ': _)  = 'True
  Elem x (_ ': xs) = Elem x xs

class Handle (handles :: Bool) eff t m where
  handle
    :: (eff (t m) => t m a)
    -> ((MonadTransControl t, eff m) => t m a)
    -> EffT t m a

instance eff (t m) => Handle 'True eff t m where
  handle m _ = EffT m
  {-# INLINE handle #-}

instance (MonadTransControl t, eff m) => Handle 'False eff t m where
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
  --      'MonadTransControl' instance and @m@ has an instance of @eff@.
  --
  -- Each higher-order method in the 'EffT' instance for a given effect should use 'sendWith' to
  -- specify how it ought to be lifted through effect handlers. For example, the definition of
  -- 'Control.Effect.Reader.local' looks like this:
  --
  -- @
  -- 'Control.Effect.Reader.local' f m = 'sendWith' @('Control.Effect.Reader.Reader' r)
  --   ('Control.Effect.Reader.local' f ('runEffT' m))
  --   ('controlT' '$' \\lower -> 'Control.Effect.Reader.local' f (lower '$' 'runEffT' m))
  -- @
  --
  -- With this instance in place, @'Reader' r@ can automatically be used with @'EffT' t m a@.
  -- Transformers that can handle the @'Reader' r@ effect (i.e. ones for which
  -- @'Handles' t ('Reader' r) ~ ''True'@) will use their @'Reader' r@ instances, while other
  -- transformers will delegate to the underlying monad.
  sendWith
    :: (eff (t m) => t m a)
    -- ^ An action to run in the current handler.
    -> ((MonadTransControl t, eff m) => t m a)
    -- ^ An action that delegates to the underlying monad.
    -> EffT t m a

instance (Monad m, Handle (Handles t eff) eff t m) => Send eff t m where
  sendWith = handle @(Handles t eff) @eff
  {-# INLINE sendWith #-}

-- | Using 'MonadTransControl', lifts a higher-order effectful operation into the underlying monad.
-- It is named by analogy to 'control', since both are intended for lifting “control operations,”
-- i.e. operations that affect control flow.
--
-- @'controlT' f@ is equivalent to @'restoreT' '.' 'pure' =<< 'liftWith' f@, but it is rare that
-- 'restoreT' or 'liftWith' need to be used directly.
controlT :: (MonadTransControl t, Monad m, Monad (t m)) => (Run t -> m (StT t a)) -> t m a
controlT f = restoreT . pure =<< liftWith f
{-# INLINE controlT #-}

type family All (cs :: [k -> Constraint]) (a :: k) :: Constraint where
  All '[]       _ = ()
  All (c ': cs) a = (c a, All cs a)

-- | A helper type for combining effect constraints: @('Can' '[e1, e2, e3, ..., en] m)@ is
-- equivalent to @(e1 m, e2 m, e3 m, ..., en m)@. The constraint @'Can' effs m@ should be read as
-- specifying that the monad @m@ /can/ perform all of the effects in the list @effs@.
class All effs m => Can (effs :: [EffectK]) m
instance All effs m => Can effs m
