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
  , Functor (HandlerState t)
  ) => Handler t where
  type HandlerState t :: Type -> Type
  hmap :: (Functor m, Functor n) => (m (HandlerState t a) -> n (HandlerState t b)) -> t m a -> t n b

-- class Handler t => Accumulate t where
--   {-# MINIMAL accumulate | hmapS #-}
--
--   accumulate :: Functor m => t (Compose m ((,) s)) a -> t m (s, a)
--   accumulate = hmapS getCompose
--   {-# INLINE accumulate #-}
--
--   hmapS :: (Functor m, Functor n) => (forall b. m b -> n (s, b)) -> t m a -> t n (s, a)
--   hmapS f = accumulate . hmap (Compose . f)
--   {-# INLINABLE hmapS #-}

class Handler t => Scoped t where
  -- | Lifts a scoped operation with support for suspension and resumption.
  scoped
    :: (Functor m, Functor n)
    => ((c -> m (HandlerState t a)) -> n (HandlerState t b))
    -- ^ Action to run the first time control enters the scoped region.
    -> (m (HandlerState t a) -> n (HandlerState t b))
    -- ^ Action to run on subsequent reentry into the scoped region.
    -> (c -> t m a) -> t n b

-- newtype Choices r a = Choices { runChoices :: (a -> r) -> r }
--   deriving (Functor, Applicative, Monad) via Cont r

class Handler t => Choice t where
  choice
    :: (Functor m, Functor n)
    => t m a -> (m (HandlerState t a) -> t n a)
    -- ^ Make a choice by extending the continuation.
    -> ((t m a -> m (HandlerState t a)) -> n (HandlerState t a))
    -- ^ Make a choice via state threading.
    -> t n a

  -- choice
  --   :: (Functor m, Functor n)
  --   => (forall b. (t m a -> (m b -> n b) -> n b) -> n b)
  --   -> t n a

  -- choice
  --   :: (Functor m, Functor n)
  --   => (forall b f. Applicative f => (t m a -> f (m b)) -> f (n b))
  --   -> t n a

  -- choice
  --   :: (Functor m, Functor n)
  --   => (forall b. m b -> (c -> m b) -> n b)
  --   -> t m a -> (c -> t m a) -> t n a
  --
  -- choice_
  --   :: (Functor m, Functor n)
  --   => (forall b. m b -> m b -> n b)
  --   -> t m a -> t m a -> t n a
  -- choice_ f m1 m2 = choice (\m g -> f m (g ())) m1 (const m2)
  -- {-# INLINE choice_ #-}

instance Handler IdentityT where
  type HandlerState IdentityT = Identity
  hmap f = mapIdentityT (fmap runIdentity . f . fmap Identity)
  {-# INLINABLE hmap #-}
instance Scoped IdentityT where
  scoped f _ k = IdentityT $ runIdentity <$> f (fmap Identity . runIdentityT . k)
  {-# INLINABLE scoped #-}
instance Choice IdentityT where
  choice _ _ f = IdentityT $ runIdentity <$> f (fmap Identity . runIdentityT)
  {-# INLINABLE choice #-}

instance Handler (ReaderT r) where
  type HandlerState (ReaderT r) = Identity
  hmap f = mapReaderT (fmap runIdentity . f . fmap Identity)
  {-# INLINABLE hmap #-}
instance Scoped (ReaderT r) where
  scoped f _ k = ReaderT $ \r -> runIdentity <$> f (fmap Identity . flip runReaderT r . k)
  {-# INLINABLE scoped #-}
instance Choice (ReaderT r) where
  choice _ _ f = ReaderT $ \r -> runIdentity <$> f (fmap Identity . flip runReaderT r)
  {-# INLINABLE choice #-}

instance Handler (ExceptT e) where
  type HandlerState (ExceptT e) = Either e
  hmap = mapExceptT
  {-# INLINE hmap #-}
instance Scoped (ExceptT e) where
  scoped f _ k = ExceptT $ f (runExceptT . k)
  {-# INLINABLE scoped #-}
instance Choice (ExceptT e) where
  choice _ _ f = ExceptT $ f runExceptT
  {-# INLINABLE choice #-}

newtype Flip p a b = Flip { unFlip :: p b a }
instance Bifunctor p => Functor (Flip p a) where
  fmap f = Flip . first f . unFlip
  {-# INLINE fmap #-}

instance Handler (Lazy.StateT s) where
  type HandlerState (Lazy.StateT s) = Flip (,) s
  hmap f = Lazy.mapStateT (fmap unFlip . f . fmap Flip)
  {-# INLINABLE hmap #-}
instance Scoped (Lazy.StateT s) where
  scoped f _ k = Lazy.StateT $ \s -> unFlip <$> f (fmap Flip . flip Lazy.runStateT s . k)
  {-# INLINABLE scoped #-}
instance Choice (Lazy.StateT s) where
  choice _ _ f = Lazy.StateT $ \s -> unFlip <$> f (fmap Flip . flip Lazy.runStateT s)
  {-# INLINABLE choice #-}

instance Handler (Strict.StateT s) where
  type HandlerState (Strict.StateT s) = Flip (,) s
  hmap f = Strict.mapStateT (fmap unFlip . f . fmap Flip)
  {-# INLINABLE hmap #-}
instance Scoped (Strict.StateT s) where
  scoped f _ k = Strict.StateT $ \s -> unFlip <$> f (fmap Flip . flip Strict.runStateT s . k)
  {-# INLINABLE scoped #-}
instance Choice (Strict.StateT s) where
  choice _ _ f = Strict.StateT $ \s -> unFlip <$> f (fmap Flip . flip Strict.runStateT s)
  {-# INLINABLE choice #-}

instance Monoid w => Handler (Lazy.WriterT w) where
  type HandlerState (Lazy.WriterT w) = Flip (,) w
  hmap f = Lazy.mapWriterT (fmap unFlip . f . fmap Flip)
  {-# INLINABLE hmap #-}
instance Monoid w => Scoped (Lazy.WriterT w) where
  scoped f _ k = Lazy.WriterT $ unFlip <$> f (fmap Flip . Lazy.runWriterT . k)
  {-# INLINEABLE scoped #-}
instance Monoid w => Choice (Lazy.WriterT w) where
  choice _ _ f = Lazy.WriterT $ unFlip <$> f (fmap Flip . Lazy.runWriterT)
  {-# INLINABLE choice #-}

instance Monoid w => Handler (Strict.WriterT w) where
  type HandlerState (Strict.WriterT w) = Flip (,) w
  hmap f = Strict.mapWriterT (fmap unFlip . f . fmap Flip)
  {-# INLINABLE hmap #-}
instance Monoid w => Scoped (Strict.WriterT w) where
  scoped f _ k = Strict.WriterT $ unFlip <$> f (fmap Flip . Strict.runWriterT . k)
  {-# INLINEABLE scoped #-}
instance Monoid w => Choice (Strict.WriterT w) where
  choice _ _ f = Strict.WriterT $ unFlip <$> f (fmap Flip . Strict.runWriterT)
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
  type EffsState ts :: Type -> Type
  hmapHandler
    :: (m (EffsState ts a) -> n (EffsState ts b))
    -> HandlerT tag ts m a -> HandlerT tag ts n b
instance (Functor m, Functor n) => HandlerHandler tag '[] m n where
  type EffsState '[] = Identity
  hmapHandler f = HandlerT . fmap runIdentity . f . fmap Identity . runHandlerT
  {-# INLINABLE hmapHandler #-}
instance (Handler t, HandlerHandler tag ts m n) => HandlerHandler tag (t ': ts) m n where
  type EffsState (t ': ts) = Compose (EffsState ts) (HandlerState (EffT t))
  hmapHandler f =
    let f' = runHandlerT . hmapHandler @tag @ts (fmap getCompose . f . fmap Compose) . HandlerT
    in  HandlerT . hmap f' . runHandlerT
  {-# INLINABLE hmapHandler #-}

instance
  ( forall m. Functor m => Functor (HandlerT tag ts m)
  , forall m. Monad m => Monad (HandlerT tag ts m)
  , forall m. Monad m => MonadTransHandler tag ts m
  , forall m n. (Functor m, Functor n) => HandlerHandler tag ts m n
  , Functor (EffsState ts)
  ) => Handler (HandlerT tag ts) where
  type HandlerState (HandlerT tag ts) = EffsState ts
  hmap = hmapHandler
  {-# INLINE hmap #-}

-- -- | An __internal__ helper class used to work around GHC’s inability to handle quantified
-- -- constraints over type families. The constraint @(forall m. c m => 'OverEffs' c ts m)@ is morally
-- -- equivalent to @(forall m. c m => c ('EffsT' ts m))@, but the latter is not allowed by GHC. The
-- -- cost of this less direct encoding is that instances must be manually brought into scope using
-- -- 'overEffs' and visible type application.
-- class OverEffs c ts m where
--   overEffs :: (c (EffsT ts m) => r) -> r
-- instance c (EffsT ts m) => OverEffs c ts m where
--   overEffs = id
--   {-# INLINE overEffs #-}

-- -- | An __internal__ helper class used to implement 'MonadTrans' and 'MonadTransControl' instances
-- -- for 'HandlerT'. This allows us to avoid making 'HandlerT' a data family by using 'inductHandler'
-- -- to perform induction over the type-level list of handlers. (We want to avoid making 'HandlerT' a
-- -- data family so that the interface is simpler, as it allows 'runHandlerT' to return an ordinary
-- -- stack of 'EffT' transformers.)
-- class InductHandler c tag ts where
--   inductHandler
--     :: (ts ~ '[] => r)
--     -> (forall t ts'.
--          ( ts ~ (t ': ts')
--          , c (EffT t)
--          , c (HandlerT tag ts')
--          , forall m. Functor m => OverEffs Functor ts' m
--          , forall m. Monad m => OverEffs Monad ts' m
--          )
--        => Proxy ts -> r)
--     -> r
-- instance InductHandler c tag '[] where
--   inductHandler a _ = a
--   {-# INLINE inductHandler #-}
-- instance
--   ( forall m. Functor m => OverEffs Functor ts m
--   , forall m. Monad m => OverEffs Monad ts m
--   , c (EffT t), c (HandlerT tag ts)
--   ) => InductHandler c tag (t ': ts) where
--   inductHandler _ b = b (Proxy @(t ': ts))
--   {-# INLINE inductHandler #-}
--
-- instance InductHandler MonadTrans tag ts => MonadTrans (HandlerT tag ts) where
--   lift :: forall m a. Monad m => m a -> HandlerT tag ts m a
--   lift = inductHandler @MonadTrans @tag @ts HandlerT $
--     \(_ :: Proxy (t ': ts')) -> overEffs @Monad @ts' @m $
--       HandlerT . lift . runHandlerT . lift @(HandlerT tag ts')
--   {-# INLINABLE lift #-}
--
-- instance
--   ( MonadTrans (HandlerT tag ts)
--   , forall m. Functor m => Functor (HandlerT tag ts m)
--   , forall m. Monad m => Monad (HandlerT tag ts m)
--   , InductHandler Handler tag ts
--   ) => Handler (HandlerT tag ts) where
--
--   hmap
--     :: forall m n a. (Functor m, Functor n)
--     => (forall b. m b -> n b) -> HandlerT tag ts m a -> HandlerT tag ts n a
--   hmap f = inductHandler @Handler @tag @ts (HandlerT . f . runHandlerT) $
--     \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
--       HandlerT . hmap (runHandlerT . hmap @(HandlerT tag ts') f . HandlerT) . runHandlerT
--   {-# INLINABLE hmap #-}
--
-- instance (Handler (HandlerT tag ts), InductHandler Scoped tag ts) => Scoped (HandlerT tag ts) where
--   scoped
--     :: forall m n c a. (Functor m, Functor n)
--     => (forall b. (c -> m b) -> n b)
--     -> (forall b. m b -> n b)
--     -> (c -> HandlerT tag ts m a) -> HandlerT tag ts n a
--   scoped f g k = inductHandler @Scoped @tag @ts (HandlerT $ f (runHandlerT . k)) $
--     \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
--       let f' :: forall b. (c -> EffsT ts' m b) -> EffsT ts' n b
--           f' k' = runHandlerT $ scoped @(HandlerT tag ts') f g (HandlerT . k')
--           g' :: forall b. EffsT ts' m b -> EffsT ts' n b
--           g' = runHandlerT . hmap @(HandlerT tag ts') g . HandlerT
--       in HandlerT $ scoped f' g' (runHandlerT . k)
--   {-# INLINABLE scoped #-}

-- instance (Handler (HandlerT tag ts), InductHandler Choice tag ts) => Choice (HandlerT tag ts) where
--   choice
--     :: forall m n a. (Functor m, Functor n)
--     => (forall b. (HandlerT tag ts m a -> (m b -> n b) -> n b) -> n b)
--     -> HandlerT tag ts n a
--   choice f = inductHandler @Choice @tag @ts (HandlerT $ f $ \m k -> k $ runHandlerT m) $
--     \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
--       HandlerT $ choice @(EffT t) $ \chooseT ->
--         runHandlerT $ choice @(HandlerT tag ts') @m @n $ \chooseTs ->
--           f $ \m k -> chooseT (runHandlerT m) $ \m' ->
--             chooseTs (HandlerT m') k


  -- choice
  --   :: forall m n a. (Functor m, Functor n)
  --   => (forall b f. Applicative f => (HandlerT tag ts m a -> f (m b)) -> f (n b))
  --   -> HandlerT tag ts n a
  -- choice f = inductHandler @Choice @tag @ts (HandlerT $ runIdentity $ f (Identity . runHandlerT)) $
  --   \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
  --     HandlerT $ choice $ \(chooseT :: EffT t (EffsT ts' m) a -> f1 (EffsT ts' m b)) ->
  --       choice @(HandlerT tag ts') @m @n $ \(chooseTs :: HandlerT tag ts' m b -> f2 (m c)) ->
  --         let choose :: HandlerT tag ts m a -> Compose f1 f2 (m c)
  --             choose = Compose . fmap (chooseTs . HandlerT) . chooseT . runHandlerT
  --         in getCompose $ f @c choose

  -- choice
  --   :: forall m n c a. (Functor m, Functor n)
  --   => (forall b. m b -> (c -> m b) -> n b)
  --   -> HandlerT tag ts m a -> (c -> HandlerT tag ts m a) -> HandlerT tag ts n a
  -- choice f m g = inductHandler @Choice @tag @ts (HandlerT $ f (runHandlerT m) (runHandlerT . g)) $
  --   \(_ :: Proxy (t ': ts')) -> overEffs @Functor @ts' @m $ overEffs @Functor @ts' @n $
  --     let f' :: forall b. EffsT ts' m b -> (c -> EffsT ts' m b) -> EffsT ts' n b
  --         f' m' g' = runHandlerT $ choice @(HandlerT tag ts') @m @n f (HandlerT m') (HandlerT . g')
  --     in HandlerT $ choice f' (runHandlerT m) (runHandlerT . g)
  -- {-# INLINABLE choice #-}
