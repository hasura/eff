{-# LANGUAGE UndecidableInstances #-}

-- | This module provides a set of classes and operations for safe resource allocation and disposal.
module Control.Effect.Resource (
  -- * Masking interrupts
    Mask(..)
  , mask_
  , uninterruptibleMask_
  -- * Registering cleanup actions
  , MonadUnwind(..)
  -- * Safe resource allocation and disposal
  , Resource
  , finally
  , bracket
  , bracket_
  , bracketOnError
  , bracketOnError_
  ) where

import qualified Control.Exception as IO
import qualified Control.Monad.Trans.Except as Trans

import Control.Effect.Internal
import Control.Handler.Internal
import Control.Monad.Trans.Except (ExceptT(..), runExceptT)
import Control.Monad.Trans.Reader (ReaderT(..), runReaderT)
import Control.Monad.Trans.State.Strict (StateT(..), runStateT)
import Data.Coerce
import Data.Functor.Identity

-- | An effect that provides the ability to temporarily mask asynchronous interrupts.
--
-- Unlike most effects, this effect does not have its own handler; there is no separate @runMask@
-- operation. This is because the usual handler for 'Mask' is 'IO', which is always at the base of
-- a monad transformer stack.
--
-- 'Mask' may be used in pure computations (where both 'mask' and 'uninterruptibleMask' are no-ops),
-- but it can only be discharged by 'runIdentity', which serves as a proof that the computation is,
-- in fact, pure.
class Monad m => Mask m where
  -- | Executes a computation with asynchronous interrupts masked; see
  -- @"Control.Exception".'IO.mask'@ for details.
  mask :: ((forall a. m a -> m a) -> m b) -> m b
  -- | Executes a computation with asynchronous interrupts uninterruptibly masked.
  -- __This should be used with great care__; see @"Control.Exception".'IO.uninterruptibleMask'@ for
  -- details.
  uninterruptibleMask :: ((forall a. m a -> m a) -> m b) -> m b

-- | Like 'mask', but does not pass a @restore@ action to its argument.
mask_ :: Mask m => m a -> m a
mask_ m = mask $ \_ -> m
{-# INLINE mask_ #-}

-- | Like 'uninterruptibleMask', but does not pass a @restore@ action to its argument.
uninterruptibleMask_ :: Mask m => m a -> m a
uninterruptibleMask_ m = uninterruptibleMask $ \_ -> m
{-# INLINE uninterruptibleMask_ #-}

instance Mask Identity where
  mask f = f id
  {-# INLINE mask #-}
  uninterruptibleMask f = f id
  {-# INLINE uninterruptibleMask #-}

instance Mask IO where
  mask = IO.mask
  {-# INLINE mask #-}
  uninterruptibleMask = IO.uninterruptibleMask
  {-# INLINE uninterruptibleMask #-}

-- This is a small wrapper type to avoid impredicativity when lifting via 'scoped'.
newtype Restore m = Restore (forall a. m a -> m a)

liftMask
  :: (Scoped t, Mask m)
  => (forall c. ((forall a. m a -> m a) -> m c) -> m c)
  -> ((forall a. t m a -> t m a) -> t m b) -> t m b
liftMask mask' f = scoped
  (\f' -> mask' $ \restore -> f' $ Restore restore)
  -- Note: this is technically a bit cheaty. When resuming a computation suspended inside of 'mask',
  -- we just wrap it in a fresh call to 'mask_' and hope for the best. This works out for 'IO'
  -- because GHC’s implementation of 'mask' does not require the restore function actually be
  -- invoked inside the dynamic extent of the call to 'mask', and it will always restore the masking
  -- state to whatever it was when 'mask' was originally invoked.
  --
  -- In theory this could go slightly wrong if some non-'IO' handler were to require a more careful
  -- semantics. However, it is monumentally unlikely that anyone will ever actually define a
  -- non-'IO' handler for 'Mask' in the first place. Therefore, we do the simple thing here, and we
  -- can be more careful if anyone ever somehow bumps into it.
  (\m -> mask' $ const m)
  (\(Restore restore) -> f (hmap restore))
{-# INLINABLE liftMask #-}

instance (Scoped t, Mask m) => Mask (LiftT t m) where
  mask = liftMask mask
  {-# INLINE mask #-}
  uninterruptibleMask = liftMask uninterruptibleMask
  {-# INLINE uninterruptibleMask #-}

instance Send Mask t m => Mask (EffT t m) where
  mask f = send @Mask $ mask $ \restore ->
    coerce $ f $ \(m :: EffT t m a) -> coerce $ restore @a $ coerce m
  {-# INLINE mask #-}
  uninterruptibleMask f = send @Mask $ uninterruptibleMask $ \restore ->
    coerce $ f $ \(m :: EffT t m a) -> coerce $ restore @a $ coerce m
  {-# INLINE uninterruptibleMask #-}

-- | The class of monads that support registering cleanup actions on failure. Note that this is
-- __not__ an effect; it cannot be automatically lifted through 'EffT' the way effects can. Doing so
-- would be unsafe, as different handlers may provide arbitrarily different notions of failure, and
-- they must supply 'MonadUnwind' instances to ensure those failures are not ignored. However, note
-- that any handlers defined using 'HandlerT' do /not/ need their own 'MonadUnwind' instances, as
-- they will inherit the instance of their underlying handlers.
class Monad m => MonadUnwind m where
  -- | @(/a/ `'onError'` /b/)@ runs @/a/@. If and only if it fails with an error, @/b/@ is
  -- executed for side effects (with asynchronous exceptions masked, if relevant), after which the
  -- error is re-raised. If @/b/@ fails with an error, its error takes priority over the error
  -- raised by @/a/@.
  --
  -- 'onError' /cannot/ generally be used to ensure the disposal of an acquired resource because an
  -- asynchronous exception might be raised after the resource is acquired but before the exception
  -- handler is installed. For safe resource management, use 'bracket' or 'bracketOnError_' instead.
  --
  -- Note that because the error is re-raised after @/b/@ is executed, changes to the monadic state
  -- made by @/b/@ will be discarded for any effects handled more locally than the effect that
  -- triggered the failure.
  onError :: m a -> m b -> m a

instance MonadUnwind Identity where
  onError a _ = a
  {-# INLINE onError #-}

instance MonadUnwind IO where
  onError = IO.onException
  {-# INLINE onError #-}

deriving newtype instance MonadUnwind (t m) => MonadUnwind (EffT t m)
deriving newtype instance MonadUnwind (EffsT ts m) => MonadUnwind (HandlerT tag ts m)

instance MonadUnwind m => MonadUnwind (ReaderT r m) where
  onError action cleanup = ReaderT $ \r -> onError (runReaderT action r) (runReaderT cleanup r)
  {-# INLINABLE onError #-}
instance MonadUnwind m => MonadUnwind (StateT r m) where
  onError action cleanup = StateT $ \s -> onError (runStateT action s) (runStateT cleanup s)
  {-# INLINABLE onError #-}

instance MonadUnwind m => MonadUnwind (ExceptT e m) where
  onError action cleanup =
    ExceptT $ onError (runExceptT action) (runExceptT cleanup) >>= \case
      -- note: need to take care to ensure an error produced by the cleanup action takes priority
      -- over the error produced by the primary action
      Left e -> runExceptT (cleanup *> Trans.throwE e)
      Right x -> pure (Right x)
  {-# INLINABLE onError #-}

-- | @('Resource' m)@ is a constraint synonym for @('Mask' m, 'MonadUnwind' m)@, which together
-- provide the operations necessary for safe resource allocation and disposal. The most frequently
-- used operations of 'Resource' are 'bracket' and 'bracketOnError'.
class (Mask m, MonadUnwind m) => Resource m
instance (Mask m, MonadUnwind m) => Resource m

-- | Like 'onError', but the action provided for the second argument is unconditionally
-- executed, whether an error was raised or not.
finally :: Resource m => m a -> m b -> m a
finally action cleanup = mask $ \restore ->
  (restore action `onError` cleanup) <* cleanup
{-# INLINABLE finally #-}

-- | Safely acquires a resource for the dynamic extent of a nested computation given actions to
-- acquire and dispose it. See also @"Control.Exception".'IO.bracket'@.
bracket
  :: Resource m
  => m a -- ^ Acquire some resource.
  -> (a -> m c) -- ^ Dispose the resource.
  -> (a -> m b) -- ^ Use the resource.
  -> m b
bracket acquire release use = mask $ \restore -> do
  a <- acquire
  (restore (use a) `onError` release a) <* release a
{-# INLINABLE bracket #-}

-- | Like 'bracket', but the return value from the first argument is ignored.
bracket_ :: Resource m => m a -> m c -> m b -> m b
bracket_ acquire release use = bracket acquire (const release) (const use)
{-# INLINABLE bracket_ #-}

-- | Like 'bracket', but the dispose action is only executed if an error is raised during the
-- dynamic extent of the primary computation.
bracketOnError
  :: Resource m
  => m a -- ^ Acquire some resource.
  -> (a -> m c) -- ^ Dispose the resource.
  -> (a -> m b) -- ^ Use the resource.
  -> m b
bracketOnError acquire release use = mask $ \restore -> do
  a <- acquire
  restore (use a) `onError` release a
{-# INLINABLE bracketOnError #-}

-- | Like 'bracketOnError', but the return value from the first argument is ignored.
bracketOnError_ :: Resource m => m a -> m c -> m b -> m b
bracketOnError_ acquire release use = bracketOnError acquire (const release) (const use)
{-# INLINABLE bracketOnError_ #-}
