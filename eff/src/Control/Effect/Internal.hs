{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Effect.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Data.Coerce
import Data.Kind (Constraint, Type)
import Data.Type.Coercion
import GHC.Generics (Generic, Generic1)
-- import GHC.TypeLits (TypeError, ErrorMessage(..))

import Control.Handler.Internal

-- | The kind of effects, which are classes of monads.
type EffectK = (Type -> Type) -> Constraint

newtype LiftT (t :: HandlerK) m a = LiftT { runLiftT :: t m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance Handler t => Handler (LiftT t) where
  newtype HandlerState (LiftT t) m r a = LiftTState { runLiftTState :: HandlerState t m r a }
  hmap f = LiftT . hmap (fmap runLiftTState . f . fmap LiftTState) . runLiftT
  {-# INLINABLE hmap #-}

deriving newtype instance Eq (HandlerState t m r a) => Eq (HandlerState (LiftT t) m r a)
deriving newtype instance Ord (HandlerState t m r a) => Ord (HandlerState (LiftT t) m r a)
deriving newtype instance Show (HandlerState t m r a) => Show (HandlerState (LiftT t) m r a)
deriving newtype instance Read (HandlerState t m r a) => Read (HandlerState (LiftT t) m r a)
deriving newtype instance Semigroup (HandlerState t m r a) => Semigroup (HandlerState (LiftT t) m r a)
deriving newtype instance Monoid (HandlerState t m r a) => Monoid (HandlerState (LiftT t) m r a)
deriving newtype instance Generic (HandlerState t m r a) => Generic (HandlerState (LiftT t) m r a)
deriving newtype instance Generic1 (HandlerState t m r) => Generic1 (HandlerState (LiftT t) m r)
deriving newtype instance Functor (HandlerState t m r) => Functor (HandlerState (LiftT t) m r)
deriving newtype instance Applicative (HandlerState t m r) => Applicative (HandlerState (LiftT t) m r)
deriving newtype instance Alternative (HandlerState t m r) => Alternative (HandlerState (LiftT t) m r)
deriving newtype instance Monad (HandlerState t m r) => Monad (HandlerState (LiftT t) m r)
deriving newtype instance MonadPlus (HandlerState t m r) => MonadPlus (HandlerState (LiftT t) m r)

instance Scoped t => Scoped (LiftT t) where
  scoped f g k = LiftT $ scoped
    (\h -> coerce <$> f (fmap coerce . h))
    (fmap coerce . g . fmap coerce)
    (coerce k)
  {-# INLINABLE scoped #-}

instance Choice t => Choice (LiftT t) where
  choice m f g = LiftT $ choice
    (coerce m) (\m' -> coerce $ f (coerce <$> m'))
    (\choose -> coerce <$> g (fmap coerce . choose . coerce))
  {-# INLINABLE choice #-}

instance (Alternative m, Monad m, Choice t) => Alternative (LiftT t m) where
  empty = lift empty
  {-# INLINE empty #-}
  a <|> b = choice a (\a' -> hmap (a' <|>) b) (\choose -> choose a <|> choose b)
  {-# INLINE (<|>) #-}

instance (Alternative m, Monad m, Choice t) => MonadPlus (LiftT t m)

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
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

instance Handler t => Handler (EffT t) where
  newtype HandlerState (EffT t) m r a = EffTState { runEffTState :: HandlerState t m r a }
  hmap f = EffT . hmap (fmap runEffTState . f . fmap EffTState) . runEffT
  {-# INLINABLE hmap #-}

deriving newtype instance Eq (HandlerState t m r a) => Eq (HandlerState (EffT t) m r a)
deriving newtype instance Ord (HandlerState t m r a) => Ord (HandlerState (EffT t) m r a)
deriving newtype instance Show (HandlerState t m r a) => Show (HandlerState (EffT t) m r a)
deriving newtype instance Read (HandlerState t m r a) => Read (HandlerState (EffT t) m r a)
deriving newtype instance Semigroup (HandlerState t m r a) => Semigroup (HandlerState (EffT t) m r a)
deriving newtype instance Monoid (HandlerState t m r a) => Monoid (HandlerState (EffT t) m r a)
deriving newtype instance Generic (HandlerState t m r a) => Generic (HandlerState (EffT t) m r a)
deriving newtype instance Generic1 (HandlerState t m r) => Generic1 (HandlerState (EffT t) m r)
deriving newtype instance Functor (HandlerState t m r) => Functor (HandlerState (EffT t) m r)
deriving newtype instance Applicative (HandlerState t m r) => Applicative (HandlerState (EffT t) m r)
deriving newtype instance Alternative (HandlerState t m r) => Alternative (HandlerState (EffT t) m r)
deriving newtype instance Monad (HandlerState t m r) => Monad (HandlerState (EffT t) m r)
deriving newtype instance MonadPlus (HandlerState t m r) => MonadPlus (HandlerState (EffT t) m r)

instance Scoped t => Scoped (EffT t) where
  scoped f g k = EffT $ scoped
    (\h -> fmap coerce $ f (fmap coerce . h))
    (fmap coerce . g . fmap coerce)
    (coerce k)
  {-# INLINABLE scoped #-}

instance Choice t => Choice (EffT t) where
  choice m f g = EffT $ choice
    (coerce m) (\m' -> coerce $ f (coerce <$> m'))
    (\choose -> coerce <$> g (fmap coerce . choose . coerce))
  {-# INLINABLE choice #-}

instance (Send Alternative t m, Monad (t m)) => Alternative (EffT t m) where
  empty = send @Alternative $ empty
  {-# INLINE empty #-}
  a <|> b = send @Alternative $ coerce a <|> coerce b
  {-# INLINE (<|>) #-}

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

class Handle (handles :: Bool) eff (t :: HandlerK) m where
  handle :: (forall n. (eff n, Coercible (t m) n) => n a) -> t m a
instance eff (t m) => Handle 'True eff t m where
  handle m = m
  {-# INLINE handle #-}
instance HandleLift (IsHandlerT t) eff t m => Handle 'False eff t m where
  handle = handleLift @(IsHandlerT t) @eff
  {-# INLINE handle #-}

type family IsHandlerT t where
  IsHandlerT (HandlerT _ _) = 'True
  IsHandlerT _              = 'False

class HandleLift (isHandlerT :: Bool) eff (t :: HandlerK) m where
  handleLift :: (forall n. (eff n, Coercible (t m) n) => n a) -> t m a
instance eff (LiftT t m) => HandleLift 'False eff t m where
  handleLift m = coerce (m @(LiftT t m))
  {-# INLINE handleLift #-}
instance eff (LiftT IdentityT m) => HandleLift 'True eff (HandlerT tag '[]) m where
  handleLift m = coerce (m @(LiftT IdentityT m))
  {-# INLINE handleLift #-}
instance
  ( eff (LiftT t (EffT (HandlerT VoidH ts) m))
  , Coercible (t (EffsT ts m)) (t (EffT (HandlerT VoidH ts) m))
  ) => HandleLift 'True eff (HandlerT tag (t ': ts)) m where
  handleLift
    :: forall a
     . (forall n. (eff n, Coercible (HandlerT tag (t ': ts) m) n) => n a)
    -> HandlerT tag (t ': ts) m a
  handleLift m = case etaExpandCoercion @(t (EffsT ts m)) @(t (EffT (HandlerT VoidH ts) m)) @a of
    Coercion -> coerce $ m @(LiftT t (EffT (HandlerT VoidH ts) m))
    where
      etaExpandCoercion :: forall f g b. Coercible f g => Coercion (f b) (g b)
      etaExpandCoercion = Coercion
  {-# INLINE handleLift #-}

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
class (Handler t, Monad m) => Send eff t m where
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
  send :: (forall n. (eff n, Coercible (EffT t m) n) => n a) -> EffT t m a

instance (Handler t, Monad m, Handle (Handles t eff) eff t m) => Send eff t m where
  send m = EffT (handle @(Handles t eff) @eff m)
  {-# INLINE send #-}

-- type family RequiredTactics (eff :: EffectK) :: [TacticK]
-- type family DeclaredTactics eff where
--   DeclaredTactics eff = NotStuck (RequiredTactics eff) (TypeError (
--     'Text "Missing a RequiredTactics declaration for ‘" ':<>: 'ShowType eff ':<>: 'Text "’"
--     ':$$: 'Text "  " ':<>:
--     ( 'Text "(Probable fix: add a declaration of the form"
--       ':$$: 'Text "   type instance " ':<>: 'ShowType (RequiredTactics eff) ':<>: 'Text " = '[...]"
--       ':$$: 'Text " alongside the ‘" ':<>: 'ShowType eff ':<>: 'Text "’ instance for EffT.)" )))
--
-- data family Skolem k :: k
-- type family NotStuck (t :: k) err :: Constraint where
--   NotStuck (Skolem k) _ = TypeError ('Text "Internal error: NotStuck instance for Skolem was selected!")
--   NotStuck _          _ = ()

-- class Send eff t m => SendWith eff t m where
--   -- | Constructs an @'EffT' t m a@ computation for a higher-order/scoped effect @eff@ from two
--   -- actions:
--   --
--   --   1. A “run” action, which executes the effect in the @(t m)@ monad given @(t m)@ has an
--   --      instance of @eff@.
--   --
--   --   2. A “lift” action, which lifts the effect through @(t m)@ into @m@ given that @t@ has a
--   --      'Handler' instance and @m@ has an instance of @eff@.
--   --
--   -- Each higher-order method in the 'EffT' instance for a given effect should use 'sendWith' to
--   -- specify how it ought to be lifted through effect handlers. For example, the definition of
--   -- 'Control.Effect.Reader.local' looks like this:
--   --
--   -- @
--   -- 'Control.Effect.Reader.local' f m = 'sendWith' @('Control.Effect.Reader.Reader' r)
--   --   ('Control.Effect.Reader.local' f ('runEffT' m))
--   --   ('liftWith' '$' \\lower -> 'Control.Effect.Reader.local' f (lower '$' 'runEffT' m))
--   -- @
--   --
--   -- With this instance in place, @'Control.Effect.Reader.Reader' r@ can automatically be used with
--   -- @'EffT' t m a@. Transformers that can handle the @'Control.Effect.Reader.Reader' r@ effect
--   -- (i.e. ones for which @'Handles' t ('Control.Effect.Reader.Reader' r) ~ ''True'@) will use their
--   -- @'Control.Effect.Reader.Reader' r@ instances, while other transformers will delegate to the
--   -- underlying monad.
--   sendWith
--     :: DeclaredTactics eff
--     => (eff (t m) => t m a)
--     -- ^ An action to run in the current handler.
--     -> ((All (RequiredTactics eff) t, eff m) => t m a)
--     -- ^ An action that delegates to the underlying monad.
--     -> EffT t m a

-- instance
--   ( Send eff t m
--   , DeclaredTactics eff
--   , Handle (Handles t eff) eff (RequiredTactics eff) t m
--   ) => SendWith eff t m where
--   sendWith = handle @(Handles t eff) @eff @(RequiredTactics eff)
--   {-# INLINE sendWith #-}

type family All (cs :: [k -> Constraint]) (a :: k) :: Constraint where
  All '[]       _ = ()
  All (c ': cs) a = (c a, All cs a)

-- | A helper type for combining effect constraints: @('Can' '[e1, e2, e3, ..., en] m)@ is
-- equivalent to @(e1 m, e2 m, e3 m, ..., en m)@. The constraint @'Can' effs m@ should be read as
-- specifying that the monad @m@ /can/ perform all of the effects in the list @effs@.
class All effs m => Can (effs :: [EffectK]) m
instance All effs m => Can effs m
