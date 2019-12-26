{-# OPTIONS_HADDOCK not-home #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
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
import Data.Type.Coercion
import Data.Kind (Constraint, Type)

import {-# SOURCE #-} Control.Effect.Error
import {-# SOURCE #-} Control.Effect.Internal
import {-# SOURCE #-} Control.Effect.Reader
import {-# SOURCE #-} Control.Effect.State

-- #ifdef __HADDOCK_VERSION__
-- import qualified System.IO as IO
--
-- import Data.Functor
--
-- import {-# SOURCE #-} Control.Effect.NonDet
-- import {-# SOURCE #-} Control.Effect.Resource
-- import {-# SOURCE #-} Control.Effect.Writer
-- #endif

-- | The kind of effect handlers, which are monad transformers.
type HandlerK = (Type -> Type) -> Type -> Type

class (MonadTrans t, forall m. Monad m => Monad (t m)) => Handler t
instance (MonadTrans t, forall m. Monad m => Monad (t m)) => Handler t

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

{-

-- | The kind of effect handlers, which are monad transformers.
type HandlerK = (Type -> Type) -> Type -> Type
-- | The kind of lifting tactics, which are classes on monad transformers.
type TacticK = HandlerK -> Constraint

-- | The class of effect handlers, which satisfy the following properties:
--
--   * All handlers are monad transformers, which means they must have an instance of the usual
--     'MonadTrans' typeclass. Additionally, this class also adds a quantified
--     @forall m. 'Monad' m => 'Monad' (t m)@ superclass, as at the time of this writing, no such
--     superclass is provided by 'MonadTrans' (though morally it ought to be).
--
--   * Furthermore, 'Handler' imposes the additional constraint that all handlers form functors
--     whenever their argument is a functor (but not necessarily a monad). This is almost always the
--     case for all monad transformers, anyway, so 'Handler' just makes the constraint explicit.
--
--   * Finally, all handlers must support the 'hmap' operation for lifting higher-order operations
--     in the base monad into the transformed monad, which is used to lift simple higher-order
--     effect operations.
--
-- You do __not__ need to implement any instances of this class yourself if you define your effect
-- handlers in terms of existing handlers using 'HandlerT'. However, if you want to implement your
-- own “primitive” handlers, you must define an instance of this class and instances of as many of
-- the classes exported by "Control.Handler.Tactics" as your handler supports.
class
  ( MonadTrans t
  , forall m. Functor m => Functor (t m)
  , forall m. Monad m => Monad (t m)
  , forall m r. Functor (HandlerState t m r)
  ) => Handler t where
  -- | A data family that represents the additional information added to the result of some
  -- computation by the handler @t@.
  --
  -- ==== The basics
  --
  -- In most cases, the @m@ and @r@ type arguments are completely unused, so you may usually ignore
  -- them and instead think of @('HandlerState' t m r a)@ as if it were a simpler type,
  -- @('HandlerState' t a)@. Indeed, @('HandlerState' t m r)@ must be a 'Functor'
  -- /regardless of the types used for @m@ and @r@,/ which places a strong restriction on the way
  -- @m@ may be used in instances of 'HandlerState'.
  --
  -- A value of type @(m ('HandlerState' t m r a))@ is almost (though not completely) isomorphic to
  -- a value of type @(t m a)@: it encapsulates the additional information added to @m@ by @t@. For
  -- example:
  --
  --   * @('HandlerState' ('Strict.StateT' s) m r a)@ is representationally equivalent to a
  --     tuple of type @(a, s)@—it combines the result of an action with the resulting state.
  --
  --   * @('HandlerState' ('ExceptT' e) m r a)@ is representationally equivalent to
  --     @('Either' e a)@—it extends the result with the possibility of failing with an error.
  --
  -- Note that the latter example illustrates that a value of type @('HandlerState' t m r a)@ might
  -- not always actually contain an @a@!
  --
  -- ==== The gory details
  --
  -- Generally, ignoring the @m@ and @r@ type parameters is fine, so you probably /do not/ need to read
  -- any further! However, if you are implementing a particularly sophisticated effect handler from scratch,
  -- you may find all the gory details useful. Here is a full explanation:
  --
  --   * If a handler only has a single continuation (and most do), @m@ and @r@ should be completely
  --     ignored, and the above explanation applies.
  --
  --   * However, if a handler has multiple continuations, @m@ and @r@ must be used: @m@ represents
  --     the type of the base monad for each additional continuation, and @r@ represents the type of
  --     each continuation’s result, whereas @a@ is only used to represent the type of the /first/
  --     continuation’s result.
  --
  -- The above explanation is probably still a little opaque, so the remainder of this section
  -- provides an example. The canonical example of a handler with multiple continuations is
  -- 'NonDetT', which has the following representation:
  --
  -- @
  -- newtype 'NonDetT' m a = 'NonDetT' { 'runNonDetT' :: m ('Maybe' (a, 'NonDetT' m a)) }
  -- @
  --
  -- Note that the type of the base monad, @m@, appears /inside/ the result of a 'NonDetT'
  -- computation, since it holds the next branch of the computation. Therefore, @m@ must be bound on
  -- the left-hand side of the definition for @'HandlerState' 'NonDetT'@, which explains its
  -- presence in the type. However, that still does not explain the purpose of @r@.
  --
  -- To motivate @r@, consider the following hypothetical instance of 'HandlerState' for 'NonDetT'
  -- that omits the @r@ type parameter:
  --
  -- @
  -- newtype 'HandlerState' 'NonDetT' m a = NonDetTState { runNonDetTState :: 'Maybe' (a, 'NonDetT' m a) }
  -- @
  --
  -- This type has a problem. To see it, consider an operation like 'listen' from the 'Writer'
  -- effect, which extends the result with some extra information:
  --
  -- @
  -- 'listen' :: 'Writer' w m => m a -> m (w, a)
  -- @
  --
  -- When 'listen' is applied to an argument of type @(m ('HandlerState' 'NonDetT' m a))@, it will
  -- receive a result of type @(m (w, ('HandlerState' 'NonDetT' m a)))@. At that point, the caller
  -- would like to use 'fmap' to convert that result into @(m ('HandlerState' 'NonDetT' m (w, a)))@
  -- so that it may be used with 'hmap':
  --
  -- @
  -- 'listen' = 'hmap' (\\m -> 'listen' m '<&>' \\(w, a) -> (w,) '<$>' a)
  -- @
  --
  -- At this point, our hands are unfortunately tied to a 'Functor' instance that does the wrong
  -- thing: we have to apply @(w,)@ to /every/ occurrence of @a@ in the result, producing a value of
  -- type @('Maybe' ((w, a), 'NonDetT' m (w, a)))@, but that is incorrect! That associates the
  -- /same/ value for @w@ with /all/ the continuations, even though each branch might theoretically
  -- produce a different result. To make that more concrete, consider the following expression:
  --
  -- @
  -- 'listen' (/a/ '<|>' /b/)
  -- @
  --
  -- If '<|>' is handled by 'NonDetT', 'listen' ought to distribute over the arguments to '<|>',
  -- leading to the following expression:
  --
  -- @
  -- 'listen' /a/ '<|>' 'listen' /b/
  -- @
  --
  -- However, in the above example, 'listen' would only be executed /once/, and its result would be
  -- used for all future branches, making the behavior actually equivalent to this expression:
  --
  -- @
  -- do (w, x) <- 'listen' /a/
  --    'pure' (w, x) '<|>' ((w,) '<$>' /b/)
  -- @
  --
  -- That is not at all what we want! The solution is to introduce the extra @r@ parameter, then
  -- modify the definition of 'HandlerState' for 'NonDetT' to the following:
  --
  -- @
  -- newtype 'HandlerState' 'NonDetT' m r a = NonDetTState { runNonDetTState :: 'Maybe' (a, 'NonDetT' m r) }
  -- @
  --
  -- Note that @a@ now /only/ appears as the result type for the first branch of the computation,
  -- and the other branches have type @r@. Indeed, the @r@ type represents the “original result
  -- type” for some computation, which allows it to be unaffected by 'fmap'. This is visible in the
  -- type of the second argument to 'hmap':
  --
  -- @
  -- m ('HandlerState' t m a a) -> n ('HandlerState' t m a b)
  -- @
  --
  -- In the argument, @r@ and @a@ are fixed to the same type, @a@. However, although @a@ changes to
  -- @b@ in the result, @r@ remains the same. This means the resulting
  -- @n ('HandlerState' 'NonDetT' m a b)@ value has the following representation:
  --
  -- @
  -- n ('Maybe' (b, 'NonDetT' m a))
  -- @
  --
  -- Crucially, the type of the continuation has been left completely unchanged, and it has the same
  -- type as the original argument, @('NonDetT' m a)@. This means the second argument to 'hmap' can
  -- be applied a second time to the continuation for the second branch (and again and again
  -- recursively, until the result is 'Nothing'), distributing the call to 'listen' over every
  -- branch of the computation.
  data HandlerState t (m :: Type -> Type) r a

  -- | Lifts a higher-order operation in the base monad to one in the transformed monad. The
  -- operation in the base monad must be at least somewhat polymorphic in order to support threading
  -- the 'HandlerState' result through it, but it does not need to be a full natural transformation,
  -- as @('HandlerState' t m r)@ is guaranteed to be a functor.
  --
  -- Examples of operations that may be lifted with 'hmap' are 'local' and 'listen', which have the
  -- following 'LiftT' implementations:
  --
  -- @
  -- instance ('Handler' t, 'Reader' r m) => 'Reader' r ('LiftT' t m) where
  --   'local' f = 'hmap' ('local' f)
  --
  -- instance ('Handler' t, 'Writer' w m) => 'Writer' w ('LiftT' t m) where
  --   'listen' = 'hmap' (\\m -> 'listen' m '<&>' \\(w, a) -> (w,) '<$>' a)
  -- @
  --
  -- ==== Suspension and resumption
  --
  -- When using handlers that support suspension and resumption of computations, it is possible that
  -- execution will be suspended within the scope of an operation and resumed at a later time. For
  -- an example, consider the following computation:
  --
  -- @
  -- 'local' f ('pure' x '<|>' e) '>>=' g
  -- @
  --
  -- If 'Alternative' is interpreted using 'NonDetT', then the computation will leave the scope of
  -- 'local' to continue evaluating the first branch of the computation by applying @g@ to @x@. The
  -- second branch of the computation, @e@, is /suspended/, and it will only be executed at a later
  -- point in time if its result is demanded.
  --
  -- If the suspended @e@ computation is resumed, control will jump back inside the 'local'-created
  -- scope. If the handler for 'local' runs after 'NonDetT', 'local' must be lifted through
  -- 'NonDetT' using 'hmap', and its meaning is defined by the following distributive law:
  --
  -- @'hmap' /f/ (/a/ '<|>' /b/)@ ≡ @'hmap' /f/ /a/ '<|>' 'hmap' /f/ /b/@
  --
  -- Since 'local' is lifted using 'hmap', it distributes over '<|>' in the same way, enabling the
  -- following equational reasoning:
  --
  -- @
  --   'local' f ('pure' x '<|>' e) '>>=' g
  -- ≡ ('local' f ('pure' x) '>>=' g) '<|>' ('local' f e '>>=' g)
  -- ≡ ('pure' x '>>=' g) '<|>' ('local' f e '>>=' g)
  -- ≡ g x '<|>' ('local' f e '>>=' g)
  -- @
  --
  -- It is important to the consider the implications of this distributivity: any side-effects added
  -- to the computation by the function provided to 'hmap' will be /re-executed/ when the suspended
  -- computation is resumed. This is almost always the correct behavior—consider as an example an
  -- operation that acquires a lock when control enters its scope and releases it upon exit.
  -- Distributivity ensures the lock will be reacquired upon resumption.
  --
  -- If distributive behavior is /not/ desired for some reason or another, extend the computation
  -- /before/ control enters the scoped region using an explicit application of '>>='. For example,
  -- the following computation will execute @setup@ just once, before control enters the local scope
  -- created by @op@:
  --
  -- @
  -- setup '>>=' \\x -> 'hmap' op (f x)
  -- @
  hmap
    :: (Functor m, Functor n)
    => (m (HandlerState t m a a) -> n (HandlerState t m a b))
    -> t m a -> t n b

-- | The class of handlers that support lifting higher-order operations that bring values into
-- scope.
class Handler t => Scoped t where
  -- | Lifts a higher-order operation that brings a value of type @c@ into scope. Generally
  -- speaking, 'scoped' lifts an operation with a type like
  --
  -- @
  -- forall a. (c -> m a) -> n a
  -- @
  --
  -- into one with a type like:
  --
  -- @
  -- forall a. (c -> t m a) -> t n a
  -- @
  --
  -- However, when lifting a scoped operation through a handler that supports suspension and
  -- resumption of computations, scoped operations must obey the same distributivity law discussed
  -- in the documentation for 'hmap'. However, the locally-scoped value must be shared between all
  -- branches of the computation (since it is captured lexically), so the second argument to
  -- 'scoped' is instead distributed over any suspended computations and is given access to the
  -- locally-scoped value directly.
  scoped
    :: (Functor m, Functor n)
    => ((c -> m (HandlerState t m a a)) -> n (HandlerState t m a b))
    -- ^ Operation to perform the first time control enters the scoped region.
    -> (m (HandlerState t m a a) -> n (HandlerState t m a b))
    -- ^ Operation to perform on resumption of a suspended action within the scoped region.
    -> (c -> t m a) -> t n b

class Handler t => Choice t where
  choice :: Functor m => t m a -> (m (HandlerState t m a a) -> t m a) -> t m a

instance Handler IdentityT where
  newtype HandlerState IdentityT m r a = IdentityTState { runIdentityTState :: a }
    deriving (Functor)
  hmap f = mapIdentityT (fmap runIdentityTState . f . fmap IdentityTState)
  {-# INLINABLE hmap #-}
instance Scoped IdentityT where
  scoped f _ k = IdentityT $ runIdentityTState <$> f (fmap IdentityTState . runIdentityT . k)
  {-# INLINABLE scoped #-}
instance Choice IdentityT where
  choice m f = f (IdentityTState <$> runIdentityT m)
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
  choice m f = ReaderT $ \r -> runReaderT (f (ReaderTState <$> runReaderT m r)) r
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
  choice m f = f (ExceptTState <$> runExceptT m)
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
  choice m f = Lazy.StateT $ \s -> Lazy.runStateT (f (LazyStateTState <$> Lazy.runStateT m s)) s
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
  choice m f = Strict.StateT $ \s -> Strict.runStateT (f (StrictStateTState <$> Strict.runStateT m s)) s
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
  choice m f = f (LazyWriterTState <$> Lazy.runWriterT m)
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
  choice m f = f (StrictWriterTState <$> Strict.runWriterT m)
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

-}
