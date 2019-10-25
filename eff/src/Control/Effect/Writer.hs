{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Writer
  ( Writer(..)
  -- * Pure, strict @Writer@ handler
  --
  -- | Note: this handler is strict in the monoidal state to avoid space leaks, but this requires
  -- 'tell' to produce __left-associated__ uses of '<>', which can be catastrophically slow on
  -- certain monoids, most notably @[]@. To avoid pathological performance, use a data structure
  -- that supports efficient appends, such as @Data.Sequence.Seq@, or use 'Data.Semigroup.Dual' to
  -- flip the argument order of '<>' (but beware that this will cause the elements to be accumulated
  -- in reverse order).
  , runWriter
  , evalWriter
  , execWriter
  , WriterT
  ) where

import Control.Effect.Internal
import Control.Effect.State
import Control.Handler.Internal
import Control.Monad.Trans.Class
import Data.Functor

-- | @'Writer' w@ is an effect that allows the accumulation of monoidal values of type @w@.
--
-- Instances should obey the following laws:
--
--   * @'tell' /x/ '*>' 'tell' /y/ ≡ 'tell' (/x/ '<>' /y/)@
--   * @'listen' ('tell' /x/) ≡ (/x/,) '<$>' 'tell' /x/@
--   * @'censor' /f/ ('tell' /x/) ≡ 'tell' (/f/ /x/)@
class (Monoid w, Monad m) => Writer w m where
  -- | Appends the given value to the current output.
  tell :: w -> m ()
  -- | Executes the given action and includes its output in the result.
  listen :: m a -> m (w, a)
  -- | Executes the given action and modifies its output by applying the given function.
  censor :: (w -> w) -> m a -> m a

instance (Monoid w, Monad (t m), Send (Writer w) t m) => Writer w (EffT t m) where
  tell w = send @(Writer w) (tell w)
  {-# INLINE tell #-}
  listen m = sendWith @(Writer w)
    (listen (runEffT m))
    (liftWith $ \lower -> listen (lower $ runEffT m) <&> \(w, s) -> (w,) <$> s)
  {-# INLINABLE listen #-}
  censor f m = sendWith @(Writer w)
    (censor f (runEffT m))
    (liftWith $ \lower -> censor f (lower $ runEffT m))
  {-# INLINABLE censor #-}

data WriterH
-- | This handler is implemented on top of 'StateT' rather than using a @WriterT@ implementation
-- from @transformers@ because both the strict and lazy @WriterT@ transformers leak space, and
-- @"Control.Monad.Trans.Writer.CPS"@ does not expose the @WriterT@ constructor, precluding an
-- efficient implementation of 'Handler'.
type WriterT w = HandlerT WriterH '[StateT w]
type instance Handles (WriterT w) eff = eff == Writer w

instance (Monoid w, Monad m) => Writer w (WriterT w m) where
  tell w = HandlerT $ modify (<> w)
  {-# INLINE tell #-}

  listen m = do
    (w, a) <- lift $ runWriter (EffT m)
    tell w
    pure (w, a)
  {-# INLINABLE listen #-}

  censor f m = do
    (w, a) <- lift $ runWriter (EffT m)
    tell (f w)
    pure a
  {-# INLINABLE censor #-}

runWriter :: (Monoid w, Functor m) => EffT (WriterT w) m a -> m (w, a)
runWriter = runState mempty . runHandlerT . runEffT

evalWriter :: (Monoid w, Monad m) => EffT (WriterT w) m a -> m a
evalWriter = evalState mempty . runHandlerT . runEffT

execWriter :: (Monoid w, Monad m) => EffT (WriterT w) m a -> m w
execWriter = execState mempty . runHandlerT . runEffT
