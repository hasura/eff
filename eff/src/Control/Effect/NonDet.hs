{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.NonDet where

import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
-- import Control.Monad.Trans.Cont
-- import Control.Monad.Trans.Identity
-- import Control.Effect.Internal
import Control.Handler.Internal
import Data.Functor
-- import Data.Functor.Identity
-- import Data.Coerce
-- import Data.Kind (Type)

newtype NonDetT m a = NonDetT { runNonDetT :: m (Maybe (a, NonDetT m a)) }
  deriving (Functor)

runNonDetAll :: (Monad m, Alternative f) => NonDetT m a -> m (f a)
runNonDetAll = foldlNonDet (\a b -> pure (a <|> pure b)) empty
{-# INLINABLE runNonDetAll #-}

runNonDetFirst :: (Monad m, Alternative f) => NonDetT m a -> m (f a)
runNonDetFirst = foldrNonDet (\x _ -> pure (pure x)) (pure empty)
{-# INLINABLE runNonDetFirst #-}

foldlNonDet :: Monad m => (b -> a -> m b) -> b -> NonDetT m a -> m b
foldlNonDet f b (NonDetT ma) = ma >>= \case
  Nothing       -> pure b
  Just (a, ma') -> f b a >>= \(!b') -> foldlNonDet f b' ma'
{-# INLINABLE foldlNonDet #-}

foldrNonDet :: Monad m => (a -> m b -> m b) -> m b -> NonDetT m a -> m b
foldrNonDet f mb (NonDetT ma) = ma >>= \case
  Nothing       -> mb
  Just (a, ma') -> f a (foldrNonDet f mb ma')
{-# INLINABLE foldrNonDet #-}

instance Monad m => Semigroup (NonDetT m a) where
  (<>) = (<|>)
  {-# INLINE (<>) #-}

instance Monad m => Monoid (NonDetT m a) where
  mempty = empty
  {-# INLINE mempty #-}

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

-- instance Handler NonDetT where
--   hmap f (NonDetT m) = NonDetT $ fmap (fmap $ hmap f) <$> f m
--   {-# INLINABLE hmap #-}

-- instance Accumulate NonDetT where
--   hmapS f (NonDetT m) = NonDetT $ f m <&> \(s, a) -> case a of
--     Nothing      -> Nothing
--     Just (x, m') -> Just ((s, x), hmapS f m')
--   {-# INLINABLE hmapS #-}
--
-- instance Scoped NonDetT where
--   scoped f k = NonDetT $ f $ \x -> runNonDetT (k x) <&> \case
--     Nothing -> Nothing
--     Just (x, m') -> Just (x, scoped f k m')

-- instance Choice NonDetT where
--   choice f =
--     let m1 = NonDetT $ f $ \(NonDetT m) ->
--           _
--     in _

instance MonadIO m => MonadIO (NonDetT m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance MonadBase b m => MonadBase b (NonDetT m) where
  liftBase = lift . liftBase
  {-# INLINE liftBase #-}
