{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.NonDet where

import Control.Applicative
import Control.Effect.Internal
import Control.Handler.Internal
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Functor

newtype NonDetT m a = NonDetT { runNonDetT :: m (Maybe (a, NonDetT m a)) }
  deriving (Functor)

type instance Handles NonDetT eff = eff == Alternative

runNonDetAll :: (Monad m, Alternative f) => EffT NonDetT m a -> m (f a)
runNonDetAll = foldlNonDet (\a b -> pure (a <|> pure b)) empty
{-# INLINABLE runNonDetAll #-}

runNonDetFirst :: (Monad m, Alternative f) => EffT NonDetT m a -> m (f a)
runNonDetFirst = foldrNonDet (\x _ -> pure (pure x)) (pure empty)
{-# INLINABLE runNonDetFirst #-}

foldlNonDet :: Monad m => (b -> a -> m b) -> b -> EffT NonDetT m a -> m b
foldlNonDet f b0 ma0 = loop b0 (runEffT ma0) where
  loop b ma = runNonDetT ma >>= \case
    Nothing       -> pure b
    Just (a, ma') -> f b a >>= \(!b') -> loop b' ma'
{-# INLINABLE foldlNonDet #-}

foldrNonDet :: Monad m => (a -> m b -> m b) -> m b -> EffT NonDetT m a -> m b
foldrNonDet f mb ma0 = loop (runEffT ma0) where
  loop ma = runNonDetT ma >>= \case
    Nothing       -> mb
    Just (a, ma') -> f a (loop ma')
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

instance Handler NonDetT where
  newtype HandlerState NonDetT m r a = NonDetTState { runNonDetTState :: Maybe (a, NonDetT m r) }
    deriving (Functor)
  hmap f (NonDetT m) = NonDetT $ fmap (fmap $ hmap f) . runNonDetTState <$> f (NonDetTState <$> m)
  {-# INLINABLE hmap #-}

instance Scoped NonDetT where
  scoped f g k = NonDetT $
    (runNonDetTState <$> f (fmap NonDetTState . runNonDetT . k)) <&> \case
      Nothing     -> Nothing
      Just (x, m) -> Just (x, hmap g m)
  {-# INLINABLE scoped #-}

instance Choice NonDetT where
  choice m0 f0 _ = go m0 f0 where
    go m f = NonDetT $ runNonDetT (f (NonDetTState <$> runNonDetT m)) <&> \case
      Nothing      -> Nothing
      Just (x, m') -> Just (x, go m' f)
  {-# INLINABLE choice #-}

instance MonadIO m => MonadIO (NonDetT m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance MonadBase b m => MonadBase b (NonDetT m) where
  liftBase = lift . liftBase
  {-# INLINE liftBase #-}
