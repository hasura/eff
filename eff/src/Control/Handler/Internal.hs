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
import Data.Functor.Compose
import Data.Kind (Constraint, Type)
import Data.Proxy

import {-# SOURCE #-} Control.Effect.Error
import {-# SOURCE #-} Control.Effect.Reader
import {-# SOURCE #-} Control.Effect.State

import Control.Effect.Internal

-- | The kind of effect handlers, which are monad transformers.
type HandlerK = (Type -> Type) -> Type -> Type
-- | The kind of lifting tactics, which are classes on monad transformers.
type TacticK = HandlerK -> Constraint

-- | The class of effect handlers. You do not need to implement any instances of this class yourself
-- if you define your effect handlers in terms of existing handlers using 'HandlerT'. However, if
-- you want to implement your own “primitive” handlers, you must define an instance of this class.
class (MonadTrans t, forall m. Functor m => Functor (t m), forall m. Monad m => Monad (t m)) => Handler t where
  hmap :: (Functor m, Functor n) => (forall b. m b -> n b) -> t m a -> t n a

class Handler t => Accumulate t where
  {-# MINIMAL accumulate | hmapS #-}

  accumulate :: Functor m => t (Compose m ((,) s)) a -> t m (s, a)
  accumulate = hmapS getCompose
  {-# INLINE accumulate #-}

  hmapS :: (Functor m, Functor n) => (forall b. m b -> n (s, b)) -> t m a -> t n (s, a)
  hmapS f = accumulate . hmap (Compose . f)
  {-# INLINABLE hmapS #-}

class Handler t => Choice t where
  choice :: (Functor m, Functor n) => (forall b. (t m a -> m b) -> n b) -> t n a

instance Handler IdentityT where
  hmap = mapIdentityT
  {-# INLINE hmap #-}
instance Accumulate IdentityT where
  hmapS = mapIdentityT
  {-# INLINE hmapS #-}
instance Choice IdentityT where
  choice f = IdentityT (f runIdentityT)
  {-# INLINE choice #-}

instance Handler (ReaderT r) where
  hmap = mapReaderT
  {-# INLINE hmap #-}
instance Accumulate (ReaderT r) where
  hmapS = mapReaderT
  {-# INLINE hmapS #-}
instance Choice (ReaderT r) where
  choice f = ReaderT $ \r -> f (flip runReaderT r)
  {-# INLINABLE choice #-}

instance Handler (ExceptT e) where
  hmap = mapExceptT
  {-# INLINE hmap #-}
instance Accumulate (ExceptT e) where
  hmapS f = mapExceptT (fmap sequence . f)
  {-# INLINABLE hmapS #-}
instance Choice (ExceptT e) where
  choice f = ExceptT $ f runExceptT
  {-# INLINE choice #-}

instance Handler (Lazy.StateT s) where
  hmap = Lazy.mapStateT
  {-# INLINE hmap #-}
instance Accumulate (Lazy.StateT s) where
  hmapS f = Lazy.mapStateT (fmap (\(s, (a, t)) -> ((s, a), t)) . f)
  {-# INLINABLE hmapS #-}
instance Choice (Lazy.StateT s) where
  choice f = Lazy.StateT $ \s -> f (flip Lazy.runStateT s)
  {-# INLINABLE choice #-}

instance Handler (Strict.StateT s) where
  hmap = Strict.mapStateT
  {-# INLINE hmap #-}
instance Accumulate (Strict.StateT s) where
  hmapS f = Strict.mapStateT (fmap (\(s, (a, t)) -> ((s, a), t)) . f)
  {-# INLINABLE hmapS #-}
instance Choice (Strict.StateT s) where
  choice f = Strict.StateT $ \s -> f (flip Strict.runStateT s)
  {-# INLINABLE choice #-}

instance Monoid w => Handler (Lazy.WriterT w) where
  hmap = Lazy.mapWriterT
  {-# INLINE hmap #-}
instance Monoid w => Accumulate (Lazy.WriterT w) where
  hmapS f = Lazy.mapWriterT (fmap (\(s, (a, w)) -> ((s, a), w)) . f)
  {-# INLINABLE hmapS #-}
instance Monoid w => Choice (Lazy.WriterT w) where
  choice f = Lazy.WriterT $ f Lazy.runWriterT
  {-# INLINE choice #-}

instance Monoid w => Handler (Strict.WriterT w) where
  hmap = Strict.mapWriterT
  {-# INLINE hmap #-}
instance Monoid w => Accumulate (Strict.WriterT w) where
  hmapS f = Strict.mapWriterT (fmap (\(s, (a, w)) -> ((s, a), w)) . f)
  {-# INLINABLE hmapS #-}
instance Monoid w => Choice (Strict.WriterT w) where
  choice f = Strict.WriterT $ f Strict.runWriterT
  {-# INLINE choice #-}

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

-- | An __internal__ helper class used to work around GHC’s inability to handle quantified
-- constraints over type families. The constraint @(forall m. c m => 'OverEffs' c ts m)@ is morally
-- equivalent to @(forall m. c m => c ('EffsT' ts m))@, but the latter is not allowed by GHC. The
-- cost of this less direct encoding is that instances must be manually brought into scope using
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
         , c (EffT t)
         , c (HandlerT tag ts')
         , forall m. Functor m => OverEffs Functor ts' m
         , forall m. Monad m => OverEffs Monad ts' m
         )
       => Proxy ts -> r)
    -> r
instance InductHandler c tag '[] where
  inductHandler a _ = a
  {-# INLINE inductHandler #-}
instance
  ( forall m. Functor m => OverEffs Functor ts m
  , forall m. Monad m => OverEffs Monad ts m
  , c (EffT t), c (HandlerT tag ts)
  ) => InductHandler c tag (t ': ts) where
  inductHandler _ b = b (Proxy @(t ': ts))
  {-# INLINE inductHandler #-}

instance InductHandler MonadTrans tag ts => MonadTrans (HandlerT tag ts) where
  lift :: forall m a. Monad m => m a -> HandlerT tag ts m a
  lift = inductHandler @MonadTrans @tag @ts HandlerT $
    \(_ :: Proxy (t ': ts')) -> overEffs @Monad @ts' @m $
      HandlerT . lift . runHandlerT . lift @(HandlerT tag ts')
  {-# INLINABLE lift #-}

instance
  ( MonadTrans (HandlerT tag ts)
  , forall m. Functor m => Functor (HandlerT tag ts m)
  , forall m. Monad m => Monad (HandlerT tag ts m)
  , InductHandler Handler tag ts
  ) => Handler (HandlerT tag ts) where

  hmap
    :: forall m n a. (Functor m, Functor n)
    => (forall b. m b -> n b) -> HandlerT tag ts m a -> HandlerT tag ts n a
  hmap f = inductHandler @Handler @tag @ts (HandlerT . f . runHandlerT) $
    \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
      HandlerT . hmap (runHandlerT . hmap @(HandlerT tag ts') f . HandlerT) . runHandlerT
  {-# INLINABLE hmap #-}

instance (Handler (HandlerT tag ts), InductHandler Accumulate tag ts) => Accumulate (HandlerT tag ts) where
  accumulate
    :: forall m s a. Functor m
    => HandlerT tag ts (Compose m ((,) s)) a -> HandlerT tag ts m (s, a)
  accumulate = inductHandler @Accumulate @tag @ts (HandlerT . getCompose . runHandlerT) $
    \(_ :: Proxy (t ': ts')) ->
      overEffs @Functor @ts' @m $ overEffs @Functor @ts' @(Compose m ((,) s)) $
        let accumulate' :: EffsT ts' (Compose m ((,) s)) b -> Compose (EffsT ts' m) ((,) s) b
            accumulate' = Compose . runHandlerT . accumulate @(HandlerT tag ts') @m . HandlerT
        in HandlerT . accumulate . hmap accumulate' . runHandlerT
  {-# INLINABLE accumulate #-}

  hmapS
    :: forall m n s a. (Functor m, Functor n)
    => (forall b. m b -> n (s, b)) -> HandlerT tag ts m a -> HandlerT tag ts n (s, a)
  hmapS f = inductHandler @Accumulate @tag @ts (HandlerT . f . runHandlerT) $
    \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
      HandlerT . hmapS (runHandlerT . hmapS @(HandlerT tag ts') f . HandlerT) . runHandlerT
  {-# INLINABLE hmapS #-}

instance (Handler (HandlerT tag ts), InductHandler Choice tag ts) => Choice (HandlerT tag ts) where
  choice
    :: forall m n a. (Functor m, Functor n)
    => (forall b. (HandlerT tag ts m a -> m b) -> n b) -> HandlerT tag ts n a
  choice f = inductHandler @Choice @tag @ts (HandlerT $ f runHandlerT) $
    \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
      HandlerT $ choice $ \lowerT -> runHandlerT $ choice @(HandlerT tag ts') @m @n $ \lowerTs ->
        f (lowerTs . HandlerT . lowerT . runHandlerT)
  {-# INLINABLE choice #-}
