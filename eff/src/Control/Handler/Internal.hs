{-# OPTIONS_HADDOCK not-home #-}

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
import Control.Monad.Trans.Reader (ReaderT(..), runReaderT)
import Data.Bifunctor
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Kind (Type)

import {-# SOURCE #-} Control.Effect.Error
import {-# SOURCE #-} Control.Effect.Reader
import {-# SOURCE #-} Control.Effect.State

import Control.Effect.Internal

-- | The kind of effect handlers, which are monad transformers.
type HandlerK = (Type -> Type) -> Type -> Type

-- | The class of effect handlers. You do not need to implement any instances of this class yourself
-- if you define your effect handlers in terms of existing handlers using 'HandlerT'. However, if
-- you want to implement your own “primitive” handlers, you must define an instance of this class.
class (MonadTrans t, forall m. Monad m => Monad (t m), Functor (HandlerState t)) => Handler t where
  -- | The monadic state maintained by a single handler, represented as a functor.
  type HandlerState t :: Type -> Type

  -- | Lifts a higher-order action from the base monad into the transformed monad.
  --
  -- 'liftWith' is like 'lift', but with the additional capability to “lower” certain effects from
  -- the handler monad into the base monad. Unlike 'lift', this lowering process cannot occur in a
  -- vacuum—an action of type @t m a@ cannot be arbitrarily converted into an action of type
  -- @m a@—as the handler may add some additional state on top of the base monad that cannot be
  -- produced from thin air. For a concrete example, consider the 'StateT' handler: it is not
  -- possible to write a function of type @'StateT' s m a -> a@ because somehow an initial state
  -- must be provided. Therefore, 'liftWith' constrains this lowering process in two ways:
  --
  --   1. A lowering function can only be obtained via 'liftWith', which requires already being in
  --      the handler’s monadic context.
  --
  --   2. Furthermore, the lowering function does not produce an action of type @m a@, but rather an
  --      action of type @m ('HandlerState' t a)@. The @'HandlerState' t@ functor encapsulates the
  --      additional state produced by the lowered computation so that it is not lost when the call
  --      to 'liftWith' returns.
  --
  -- To put things another way, each call to 'liftWith' effectively captures the
  -- current monadic state, embedding it inside the closure of the lowering function, and each use
  -- of the lowering function executes a computation using that state. The state is threaded through
  -- the resulting action to produce a combination of both the new state and the resulting value,
  -- which are packaged together in the @'HandlerState' t@ functor.
  --
  -- These restrictions mean that not all higher order actions can be lifted using 'liftWith'.
  -- For example, consider the following two operations:
  --
  -- @
  -- foo :: m a -> m a
  -- bar :: m 'Int' -> m ()
  -- @
  --
  -- These look remarkably similar, but the polymorphism of @foo@ makes all the difference.
  -- Implementing a lifted version of @foo@ is straightforward:
  --
  -- @
  -- foo' :: t m a -> t m a
  -- foo' m = 'liftWith' '$' \\lower -> foo (lower m)
  -- @
  --
  -- However, the same approach with 'bar' fails: applying @lower@ to the input action of type @t m
  -- Int@ produces a new action of type @m ('HandlerState' t 'Int')@, which cannot be provided to
  -- @bar@, as @bar@ wants an action of exactly @m 'Int'@. This is a fundamental restriction, as an
  -- action of type @t m 'Int'@ might not actually produce an 'Int' at all: it might fail with an
  -- error! An operation with a type like the one @bar@ has simply cannot allow arbitrary effects.
  --
  -- This limitation is a good thing, as it prevents many misuses of 'liftWith', but unfortunately
  -- it cannot prevent all of them. Consider a third operation:
  --
  -- @
  -- baz :: m a -> m ()
  -- @
  --
  -- At first blush, this operation cannot be lifted either, as @baz (lower m)@ will produce an
  -- action of type @m ()@, but 'liftWith' demands an action of type @m ('HandlerState' t ())@.
  -- However, it is technically possible to get the latter from the former by using 'lift' on the
  -- result followed immediately by @lower@. Although this typechecks, it does not do the right
  -- thing! The state changes made by the input action will be discarded, as @lower@ simply resumes
  -- using the original state.
  --
  -- The fact that such uses are permitted by 'liftWith' is a flaw in its type, but it is not clear
  -- how to prevent them without linear types. If you have an alternate formulation of 'liftWith'
  -- that does not suffer from this problem, please let the author of this library know! In the
  -- meantime, 'liftWith' must be used with some care.
  --
  -- Instances of 'Handler' should obey the following laws:
  --
  --   * @'liftWith' ('const' /m/)@ ≡ @'lift' /m/@
  --   * @'liftWith' ('$' 'lift' /m/)@ ≡ @'lift' /m/@
  liftWith
    :: Monad m
    => ((forall r. t m r -> m (HandlerState t r)) -> m (HandlerState t a))
    -> t m a

instance Handler IdentityT where
  type HandlerState IdentityT = Identity
  liftWith f = IdentityT (runIdentity <$> f (\m -> Identity <$> runIdentityT m))
  {-# INLINABLE liftWith #-}

instance Handler (ReaderT r) where
  type HandlerState (ReaderT r) = Identity
  liftWith f = ReaderT $ \r -> runIdentity <$> f (\m -> Identity <$> runReaderT m r)
  {-# INLINABLE liftWith #-}

instance Handler (ExceptT e) where
  type HandlerState (ExceptT e) = Either e
  liftWith f = coerce (f coerce)
  {-# INLINE liftWith #-}

newtype Flip p a b = Flip { unFlip :: p b a }
instance Bifunctor p => Functor (Flip p a) where
  fmap f = Flip . first f . unFlip
  {-# INLINE fmap #-}

instance Handler (Lazy.StateT s) where
  type HandlerState (Lazy.StateT s) = Flip (,) s
  liftWith f = Lazy.StateT $ \s -> unFlip <$> f (\m -> Flip <$> Lazy.runStateT m s)
  {-# INLINABLE liftWith #-}

instance Handler (Strict.StateT s) where
  type HandlerState (Strict.StateT s) = Flip (,) s
  liftWith f = Strict.StateT $ \s -> unFlip <$> f (\m -> Flip <$> Strict.runStateT m s)
  {-# INLINABLE liftWith #-}

instance Monoid w => Handler (Lazy.WriterT w) where
  type HandlerState (Lazy.WriterT w) = Flip (,) w
  liftWith f = Lazy.WriterT $ unFlip <$> f (\m -> Flip <$> Lazy.runWriterT m)
  {-# INLINABLE liftWith #-}

instance Monoid w => Handler (Strict.WriterT w) where
  type HandlerState (Strict.WriterT w) = Flip (,) w
  liftWith f = Strict.WriterT $ unFlip <$> f (\m -> Flip <$> Strict.runWriterT m)
  {-# INLINABLE liftWith #-}

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

class MonadTransHandler tag ts m => HandlerHandler tag ts m where
  type EffsState ts :: Type -> Type
  liftHandlerWith
    :: ((forall r. HandlerT tag ts m r -> m (EffsState ts r)) -> m (EffsState ts a))
    -> HandlerT tag ts m a
instance Monad m => HandlerHandler tag '[] m where
  type EffsState '[] = Identity
  liftHandlerWith f = HandlerT (runIdentity <$> f (\m -> Identity <$> runHandlerT m))
  {-# INLINABLE liftHandlerWith #-}
instance (Monad m, Handler t, HandlerHandler tag ts m) => HandlerHandler tag (t ': ts) m where
  type EffsState (t ': ts) = Compose (EffsState ts) (HandlerState t)
  liftHandlerWith f = HandlerT $ liftWith $ \lowerT ->
    runHandlerT $ liftHandlerWith @tag @ts $ \lowerTs ->
      getCompose <$> f (\m -> fmap Compose $ lowerTs $ HandlerT $ lowerT $ runHandlerT m)
  {-# INLINABLE liftHandlerWith #-}

instance
  ( forall m. Monad m => Monad (HandlerT tag ts m)
  , forall m. Monad m => HandlerHandler tag ts m
  , Functor (EffsState ts)
  ) => Handler (HandlerT tag ts) where
  type HandlerState (HandlerT tag ts) = EffsState ts
  liftWith = liftHandlerWith
  {-# INLINE liftWith #-}
