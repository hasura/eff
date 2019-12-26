{-# LANGUAGE MagicHash #-}

module Control.Monad.Wind where

import qualified Control.Exception as E

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
-- import Data.Functor
import GHC.Exts


newtype ContExc e r a = ContExc { unContExc :: (Either e a -> r) -> r }
  deriving (Functor)

instance Applicative (ContExc e r) where
  pure v = ContExc ($ Right v)
  (<*>) = ap

instance Monad (ContExc e r) where
  ContExc m >>= f = ContExc $ \k -> m $ \case
    Left e -> k (Left e)
    Right v -> unContExc (f v) k

contE :: ((a -> r) -> r) -> ContExc e r a
contE m = ContExc $ \k -> m (k . Right)

throwE :: e -> ContExc e r a
throwE e = ContExc ($ Left e)

catchE :: ContExc e r a -> (e -> ContExc e r a) -> ContExc e r a
catchE (ContExc m) f = ContExc $ \k -> m $ \case
  Left e -> unContExc (f e) k
  Right v -> k (Right v)

-- newtype ContIO r a = ContIO { unContIO :: (IO a -> IO r) -> IO r }
--   deriving (Functor)
--
-- instance Applicative (ContIO r) where
--   pure v = ContIO ($ pure v)
--   (<*>) = ap
--
-- instance Monad (ContIO r) where
--   ContIO m >>= f = ContIO $ \k -> m $ \m' -> do
--     x <- m'
--     unContIO (f x) k
--
-- runContIO :: ContIO a a -> IO a
-- runContIO (ContIO m) = m id

newtype LogicT m a
  = LogicT { unLogicT :: forall r. (a -> m r -> m r) -> m r -> m r }
  deriving (Functor)

instance Applicative (LogicT m) where
  pure v = LogicT ($ v)
  (<*>) = ap

instance Monad (LogicT m) where
  LogicT m >>= f = LogicT $ \ok -> m $ \x -> unLogicT (f x) ok

instance Alternative (LogicT m) where
  empty = LogicT (flip const)
  LogicT a <|> LogicT b = LogicT $ \ok -> a ok . b ok

instance MonadTrans LogicT where
  lift m = LogicT $ \ok bail -> m >>= flip ok bail

newtype NonDetT m a
  = NonDetT { unNonDetT :: forall r. m r -> (a -> m r) -> (m r -> m r -> m r) -> m r }
  deriving (Functor)

instance Applicative (NonDetT m) where
  pure v = NonDetT $ \_ one _ -> one v
  (<*>) = ap

instance Monad (NonDetT m) where
  NonDetT m >>= f = NonDetT $ \zero one two ->
    m zero (\x -> unNonDetT (f x) zero one two) two

instance Alternative (NonDetT m) where
  empty = NonDetT $ \zero _ _ -> zero
  NonDetT a <|> NonDetT b = NonDetT $ \zero one two ->
    two (a zero one two) (b zero one two)

instance MonadTrans NonDetT where
  lift m = NonDetT $ \_ one _ -> m >>= one

class Monad m => MonadCatch m where
  catch :: E.Exception e => m a -> (e -> m a) -> m a

instance MonadCatch m => MonadCatch (NonDetT m) where
  catch (NonDetT m) f = NonDetT $ \zero one two ->
    catch (m zero one (\a b -> _)) _

-- instance MonadCatch m => MonadCatch (LogicT m) where
--   catch (LogicT m) f = LogicT $ \ok bail ->
--

-- newtype NonDetT m a
--   = NonDetT
--   { unNonDetT :: forall r. (a -> m r) ->  -> m r }

{-

catch (throw e <|> m) f  -->  catch (throw e) f <|> catch m f

catch (throw e <|> m) f  -->  catch

catch (catch e f1) f2

-}

-- catch :: E.Exception e => ContIO r a -> (e -> ContIO r a) -> ContIO r a
-- catch (ContIO m) f = ContIO $ \k -> m $ \m' -> E.mask $ \restore -> do
--   x <- E.try @E.SomeException (restore m')
--   case x of
--     Left e -> case E.fromException e of
--       Just e' -> unContIO (f e') k
--       Nothing -> k (E.throwIO e)
--     Right v -> k (pure v)

-- class Monad m => Mask m where
--   mask :: ((forall b. m b -> m b) -> m a) -> m a
--   uninterruptibleMask :: ((forall b. m b -> m b) -> m a) -> m a
--
-- class Monad m => Wind m where
--   onEnter :: (m a -> m a) -> m a -> m a
--
--   -- | If the second argument is executed, this function /must not return!/ TODO: Figure out how to
--   -- encode that invariant in the type system. Until then, it can be captured by this law:
--   --
--   -- @((/a/ `'onAbort'` /b/) '>>=' /f/) `'onAbort'` /c/@  ≡ @(/a/ `'onAbort'` (/b/ '*>' /c/)) '>>=' /f/@
--   onAbort :: m a -> m b -> m a
--
-- finally :: (Mask m, Unwind m) => m a -> m b -> m a
-- finally a b = mask $ \restore -> (restore a `onAbort` b) <* b
-- {-# INLINABLE finally #-}
--
-- class Unwind m => Wind m where
--   onEnter ::

-- class Unwind m => Wind m where
--   onEnter :: m a -> (a -> m b) -> m b
--   onEnter
--     :: m a
--     -- ^ Action to allocate a resource the first time control enters the region.
--     -> (a -> m b)
--     -- ^ Action to run
--     -> (a -> m b -> m b)
--     -> m b
