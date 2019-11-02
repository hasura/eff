{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Handler.Internal where

import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict

import Control.Applicative
import Control.Monad
import Control.Monad.Base (MonadBase(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Reader (ReaderT(..), mapReaderT, runReaderT)
import Data.Bifunctor
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Coerce
import Data.Kind (Constraint, Type)

import {-# SOURCE #-} Control.Effect.Error
import {-# SOURCE #-} Control.Effect.Internal
import {-# SOURCE #-} Control.Effect.Reader
import {-# SOURCE #-} Control.Effect.State

-- | The kind of effect handlers, which are monad transformers.
type HandlerK = (Type -> Type) -> Type -> Type
-- | The kind of lifting tactics, which are classes on monad transformers.
type TacticK = HandlerK -> Constraint

-- | The class of effect handlers. You do not need to implement any instances of this class yourself
-- if you define your effect handlers in terms of existing handlers using 'HandlerT'. However, if
-- you want to implement your own “primitive” handlers, you must define an instance of this class.
class
  ( MonadTrans t
  , forall m. Functor m => Functor (t m)
  , forall m. Monad m => Monad (t m)
  , forall m r. Functor (HandlerState t m r)
  ) => Handler t where
  data HandlerState t (m :: Type -> Type) r a
  hmap
    :: (Functor m, Functor n)
    => (m (HandlerState t m a a) -> n (HandlerState t m a b))
    -> t m a -> t n b

class Handler t => Scoped t where
  -- | Lifts a scoped operation with support for suspension and resumption.
  scoped
    :: (Functor m, Functor n)
    => ((c -> m (HandlerState t m a a)) -> n (HandlerState t m a b))
    -- ^ Action to run the first time control enters the scoped region.
    -> (m (HandlerState t m a a) -> n (HandlerState t m a b))
    -- ^ Action to run on subsequent reentry into the scoped region.
    -> (c -> t m a) -> t n b

class Handler t => Choice t where
  choice
    :: Functor m
    => t m a -> (m (HandlerState t m a a) -> t m a)
    -- ^ Make a choice by extending the continuation.
    -> ((t m a -> m (HandlerState t m a a)) -> m (HandlerState t m a a))
    -- ^ Make a choice via state threading.
    -> t m a

instance Handler IdentityT where
  newtype HandlerState IdentityT m r a = IdentityTState { runIdentityTState :: a }
    deriving (Functor)
  hmap f = mapIdentityT (fmap runIdentityTState . f . fmap IdentityTState)
  {-# INLINABLE hmap #-}
instance Scoped IdentityT where
  scoped f _ k = IdentityT $ runIdentityTState <$> f (fmap IdentityTState . runIdentityT . k)
  {-# INLINABLE scoped #-}
instance Choice IdentityT where
  choice _ _ f = IdentityT $ runIdentityTState <$> f (fmap IdentityTState . runIdentityT)
  {-# INLINABLE choice #-}

instance Handler (ReaderT r) where
  newtype HandlerState (ReaderT r) m b a = ReaderTState { runReaderTState :: a }
    deriving (Functor)
  hmap f = mapReaderT (fmap runReaderTState . f . fmap ReaderTState)
  {-# INLINABLE hmap #-}
instance Scoped (ReaderT r) where
  scoped f _ k = ReaderT $ \r -> runReaderTState <$> f (fmap ReaderTState . flip runReaderT r . k)
  {-# INLINABLE scoped #-}
instance Choice (ReaderT r) where
  choice _ _ f = ReaderT $ \r -> runReaderTState <$> f (fmap ReaderTState . flip runReaderT r)
  {-# INLINABLE choice #-}

instance Handler (ExceptT e) where
  newtype HandlerState (ExceptT e) m r a = ExceptTState { runExceptTState :: Either e a }
    deriving newtype (Functor)
  hmap f = mapExceptT (fmap runExceptTState . f . fmap ExceptTState)
  {-# INLINABLE hmap #-}
instance Scoped (ExceptT e) where
  scoped f _ k = ExceptT $ runExceptTState <$> f (fmap ExceptTState . runExceptT . k)
  {-# INLINABLE scoped #-}
instance Choice (ExceptT e) where
  choice _ _ f = ExceptT $ runExceptTState <$> f (fmap ExceptTState . runExceptT)
  {-# INLINABLE choice #-}

newtype Flip p a b = Flip { unFlip :: p b a }
instance Bifunctor p => Functor (Flip p a) where
  fmap f = Flip . first f . unFlip
  {-# INLINE fmap #-}

instance Handler (Lazy.StateT s) where
  newtype HandlerState (Lazy.StateT s) m r a = LazyStateTState { runLazyStateTState :: (a, s) }
  hmap f = Lazy.mapStateT (fmap runLazyStateTState . f . fmap LazyStateTState)
  {-# INLINABLE hmap #-}
deriving via Flip (,) s instance Functor (HandlerState (Lazy.StateT s) m r)
instance Scoped (Lazy.StateT s) where
  scoped f _ k = Lazy.StateT $ \s ->
    runLazyStateTState <$> f (fmap LazyStateTState . flip Lazy.runStateT s . k)
  {-# INLINABLE scoped #-}
instance Choice (Lazy.StateT s) where
  choice _ _ f = Lazy.StateT $ \s ->
    runLazyStateTState <$> f (fmap LazyStateTState . flip Lazy.runStateT s)
  {-# INLINABLE choice #-}

instance Handler (Strict.StateT s) where
  newtype HandlerState (Strict.StateT s) m r a = StrictStateTState { runStrictStateTState :: (a, s) }
  hmap f = Strict.mapStateT (fmap runStrictStateTState . f . fmap StrictStateTState)
  {-# INLINABLE hmap #-}
deriving via Flip (,) s instance Functor (HandlerState (Strict.StateT s) m r)
instance Scoped (Strict.StateT s) where
  scoped f _ k = Strict.StateT $ \s ->
    runStrictStateTState <$> f (fmap StrictStateTState . flip Strict.runStateT s . k)
  {-# INLINABLE scoped #-}
instance Choice (Strict.StateT s) where
  choice _ _ f = Strict.StateT $ \s ->
    runStrictStateTState <$> f (fmap StrictStateTState . flip Strict.runStateT s)
  {-# INLINABLE choice #-}

instance Monoid w => Handler (Lazy.WriterT w) where
  newtype HandlerState (Lazy.WriterT w) m r a = LazyWriterTState { runLazyWriterTState :: (a, w) }
  hmap f = Lazy.mapWriterT (fmap runLazyWriterTState . f . fmap LazyWriterTState)
  {-# INLINABLE hmap #-}
deriving via Flip (,) w instance Functor (HandlerState (Lazy.WriterT w) m r)
instance Monoid w => Scoped (Lazy.WriterT w) where
  scoped f _ k = Lazy.WriterT $
    runLazyWriterTState <$> f (fmap LazyWriterTState . Lazy.runWriterT . k)
  {-# INLINEABLE scoped #-}
instance Monoid w => Choice (Lazy.WriterT w) where
  choice _ _ f = Lazy.WriterT $
    runLazyWriterTState <$> f (fmap LazyWriterTState . Lazy.runWriterT)
  {-# INLINABLE choice #-}

instance Monoid w => Handler (Strict.WriterT w) where
  newtype HandlerState (Strict.WriterT w) m r a = StrictWriterTState { runStrictWriterTState :: (a, w) }
  hmap f = Strict.mapWriterT (fmap runStrictWriterTState . f . fmap StrictWriterTState)
  {-# INLINABLE hmap #-}
deriving via Flip (,) w instance Functor (HandlerState (Strict.WriterT w) m r)
instance Monoid w => Scoped (Strict.WriterT w) where
  scoped f _ k = Strict.WriterT $
    runStrictWriterTState <$> f (fmap StrictWriterTState . Strict.runWriterT . k)
  {-# INLINEABLE scoped #-}
instance Monoid w => Choice (Strict.WriterT w) where
  choice _ _ f = Strict.WriterT $
    runStrictWriterTState <$> f (fmap StrictWriterTState . Strict.runWriterT)
  {-# INLINABLE choice #-}

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
type instance Handles (Strict.StateT s) eff = eff == State s

-- | A tag for use with 'HandlerT' that handles no effects. Currently not exported as part of the
-- public API, as it probably isn’t very useful for end users. However, it is currently used as part
-- of the implementation of the internal lifting machinery.
data VoidH
type instance Handles (HandlerT VoidH ts) eff = 'False

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

class Monad (EffsT ts m) => MonadTransHandler tag ts m where
  liftHandler :: m a -> HandlerT tag ts m a
instance Monad m => MonadTransHandler tag '[] m where
  liftHandler = HandlerT
  {-# INLINE liftHandler #-}
instance (Handler t, MonadTransHandler tag ts m) => MonadTransHandler tag (t ': ts) m where
  liftHandler = HandlerT . lift . runHandlerT . liftHandler @tag @ts
  {-# INLINABLE liftHandler #-}

instance (forall m. Monad m => MonadTransHandler tag ts m) => MonadTrans (HandlerT tag ts) where
  lift = liftHandler
  {-# INLINE lift #-}

class (Functor m, Functor n, Functor (EffsT ts m), Functor (EffsT ts n)) => HandlerHandler tag ts m n where
  type EffsState ts (m :: Type -> Type) r :: Type -> Type
  hmapHandler
    :: (m (EffsState ts m a a) -> n (EffsState ts m a b))
    -> HandlerT tag ts m a -> HandlerT tag ts n b
instance (Functor m, Functor n) => HandlerHandler tag '[] m n where
  type EffsState '[] m r = Identity
  hmapHandler f = HandlerT . fmap runIdentity . f . fmap Identity . runHandlerT
  {-# INLINABLE hmapHandler #-}
instance (Handler t, HandlerHandler tag ts m n) => HandlerHandler tag (t ': ts) m n where
  type EffsState (t ': ts) m r = Compose
    (EffsState ts m (HandlerState (EffT t) (EffsT ts m) r r))
    (HandlerState (EffT t) (EffsT ts m) r)
  hmapHandler f =
    let f' = runHandlerT . hmapHandler @tag @ts (fmap getCompose . f . fmap Compose) . HandlerT
    in  HandlerT . hmap f' . runHandlerT
  {-# INLINABLE hmapHandler #-}

instance
  ( forall m. Functor m => Functor (HandlerT tag ts m)
  , forall m. Monad m => Monad (HandlerT tag ts m)
  , forall m. Monad m => MonadTransHandler tag ts m
  , forall m n. (Functor m, Functor n) => HandlerHandler tag ts m n
  , forall m r. Functor (HandlerState (HandlerT tag ts) m r)
  ) => Handler (HandlerT tag ts) where
  newtype HandlerState (HandlerT tag ts) m r a = HandlerTState { runHandlerTState :: EffsState ts m r a }
  hmap f = hmapHandler (fmap coerce . f . fmap coerce)
  {-# INLINE hmap #-}
deriving newtype instance Functor (EffsState ts m r) => Functor (HandlerState (HandlerT tag ts) m r)
