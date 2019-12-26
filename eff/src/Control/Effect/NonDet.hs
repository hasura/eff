{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.NonDet
  ( NonDetT(..)
  , runAll
  , runFirst
  , foldl
  , foldr
  , uncons
  -- * Re-exports
  , Alternative(..)
  ) where

import Prelude hiding (foldl, foldr)

import Control.Applicative
import Control.Effect.Internal
import Control.Handler.Internal
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Functor

-- | An effect handler for 'Alternative' using so-called /nondeterministic execution/, which runs
-- all branches of a computation and collects some or all of their results. Actual execution is not
-- truly nondeterministic in the sense that it is somehow random; rather, 'NonDetT' models
-- nondeterministic binary choice by executing /both/ possibilities rather than choosing just one.
--
-- Although 'NonDetT' is a single, concrete handler, it is quite flexible in how it can be used, and
-- it can be useful to think about it in any of several different ways:
--
--   * When using 'runAll', '<|>' forks the computation, forming a tree, and the result is all the
--     values produced by 'pure' in the leaves. 'empty' is a leaf that produces no value. In this
--     mode, '<|>', 'empty', and '>>=' on 'NonDetT' work just like they do on @[]@, except that
--     other effects may be used as well.
--
--   * When using 'runFirst', 'empty' is a failure operation that causes the computation to
--     backtrack to the nearest alternative provided by '<|>'. The result of 'runFirst' is the first
--     result of 'runAll', except that it is lazier: 'runAll' will always run all effects that would
--     be necessary to produce all values, but 'runFirst' only performs the effects needed to
--     produce the first value.
--
--   * For more complex use cases, 'foldr' can be used, which makes 'NonDetT' behave like a lazy,
--     monadic stream. Just like with 'runAll', the result can include many values, but instead of
--     returning them all at once, a monadic action is provided to get the rest of the values. This
--     makes it possible to consume some, but not all, of the results, and only execute the effects
--     necessary to produce the results requested.
--
-- This flexibility allows 'NonDetT' to be used for many purposes, from the traversal of a search
-- space to a stateful generator.
newtype NonDetT m a = NonDetT { runNonDetT :: m (Maybe (a, NonDetT m a)) }
  deriving (Functor)

type instance Handles NonDetT eff = eff == Alternative

-- | Handles an 'Alternative' effect using 'NonDetT', collecting the results into another
-- 'Alternative'. The results are collected __strictly__, which means that /all/ effects are
-- evaluated (even if using an 'Alternative' that ignores subsequent results, such as 'Maybe').
--
-- The result is also built using a __left-associated__ sequence of '<|>' calls, which allows the
-- result to be constructed in constant space if an appropriate 'Alternative' instance is used, but
-- can lead to very poor performance for types with inefficient append operations, such as @[]@.
-- Consider using a data structure that supports efficient appends, such as @Data.Sequence.Seq@, or
-- use 'foldr'.
runAll :: (Monad m, Alternative f) => EffT NonDetT m a -> m (f a)
runAll = foldl (\a b -> pure (a <|> pure b)) empty
{-# INLINABLE runAll #-}

-- | Like 'runAll', but stops after the first result is produced, only evaluating the effects
-- necessary.
runFirst :: (Monad m, Alternative f) => EffT NonDetT m a -> m (f a)
runFirst = foldr (\x _ -> pure (pure x)) (pure empty)
{-# INLINABLE runFirst #-}

-- | A strict, monadic, left fold over 'NonDetT'. Like 'runAll', this always evaluates all effects,
-- but it can be used to accumulate the result in more flexible ways.
foldl :: Monad m => (b -> a -> m b) -> b -> EffT NonDetT m a -> m b
foldl f b0 ma0 = loop b0 (runEffT ma0) where
  loop b ma = runNonDetT ma >>= \case
    Nothing       -> pure b
    Just (a, ma') -> f b a >>= \(!b') -> loop b' ma'
{-# INLINABLE foldl #-}

-- | A lazy, monadic, right fold over 'NonDetT'. Like 'runFirst', this does not necessarily evaluate
-- all effects, so it can be used to consume infinitely-large computations, so long as the provided
-- function is sufficiently lazy in its second argument.
foldr :: Monad m => (a -> m b -> m b) -> m b -> EffT NonDetT m a -> m b
foldr f mb ma0 = loop (runEffT ma0) where
  loop ma = runNonDetT ma >>= \case
    Nothing       -> mb
    Just (a, ma') -> f a (loop ma')
{-# INLINABLE foldr #-}

-- | The most flexible way to consume the results of 'NonDetT', 'uncons' runs the provided
-- computation until it either returns a value or terminates without producing any values. In the
-- former case, it also returns a new computation, which can be consumed to access the remaining
-- values. 'uncons' is lazy, so if that computation is never used, its effects are not executed.
uncons :: Functor m => EffT NonDetT m a -> m (Maybe (a, EffT NonDetT m a))
uncons = fmap (fmap (fmap EffT)) . runNonDetT . runEffT
{-# INLINABLE uncons #-}

instance Monad m => Applicative (NonDetT m) where
  pure v = NonDetT . pure $ Just (v, empty)
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Alternative (NonDetT m) where
  empty = NonDetT $ pure Nothing
  {-# INLINE empty #-}

  NonDetT ma <|> NonDetT mb = NonDetT $ ma >>= \case
    Nothing       -> mb
    Just (a, ma') -> pure $ Just (a, ma' <|> NonDetT mb)
  {-# INLINABLE (<|>) #-}

instance Monad m => Monad (NonDetT m) where
  NonDetT mx >>= f = NonDetT $ mx >>= \case
    Nothing       -> pure Nothing
    Just (x, mx') -> runNonDetT (f x <|> (mx' >>= f))
  {-# INLINABLE (>>=) #-}

instance Monad m => MonadPlus (NonDetT m)

instance MonadTrans NonDetT where
  lift m = NonDetT $ m <&> \x -> Just (x, empty)
  {-# INLINABLE lift #-}

instance MonadIO m => MonadIO (NonDetT m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance MonadBase b m => MonadBase b (NonDetT m) where
  liftBase = lift . liftBase
  {-# INLINE liftBase #-}
