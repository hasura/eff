{-# LANGUAGE UndecidableInstances #-}

module Control.Effect2
  ( Eff
  , run

  , EffectK
  , (:<)
  , send

  , Handle
  , handle
  , bind
  , escape
  , abort
  , getS
  , putS

  , Error(..)
  , throw
  , catch
  , runError

  , Reader(..)
  , ask
  , local
  , runReader

  , State(..)
  , get
  , put
  , modify
  , runState
  , evalState
  , execState

  , NonDet(..)
  , runNonDetAll

  , type (~>)
  , (&)
  ) where

import Control.Applicative
import Control.Natural (type (~>))
import Data.Bool (bool)
import Data.Function
import Data.Tuple (swap)

import Control.Effect2.Internal

data Error e :: EffectK where
  Throw :: e -> Error e m a
  Catch :: Eff (Error e ': effs) a -> (e -> Eff effs a) -> Error e (Eff effs) a

throw :: (Error e :< effs) => e -> Eff effs a
throw = send . Throw
{-# INLINE throw #-}

catch :: (Error e :< effs) => Eff (Error e ': effs) a -> (e -> Eff effs a) -> Eff effs a
catch a b = send $ Catch a b
{-# INLINE catch #-}

runError :: Eff (Error e ': effs) a -> Eff effs (Either e a)
runError m = (Right <$> m) & handle () \case
  Throw e -> abort $ Left e
  Catch m' f -> bind (either f pure =<< runError m')

data Reader r :: EffectK where
  Ask :: Reader r m r
  Local :: (r -> r) -> Eff (Reader r ': effs) a -> Reader r (Eff effs) a

ask :: (Reader r :< effs) => Eff effs r
ask = send Ask
{-# INLINE ask #-}

local :: (Reader r :< effs) => (r -> r) -> Eff (Reader r ': effs) ~> Eff effs
local a b = send $ Local a b
{-# INLINE local #-}

runReader :: r -> Eff (Reader r ': effs) ~> Eff effs
runReader r = handle () \case
  Ask -> pure r
  Local f m -> let !r' = f r in bind $ runReader r' m

data State s :: EffectK where
  Get :: State s m s
  Put :: s -> State s m ()

get :: (State s :< effs) => Eff effs s
get = send Get
{-# INLINE get #-}

put :: (State s :< effs) => s -> Eff effs ()
put = send . Put
{-# INLINE put #-}

modify :: (State s :< effs) => (s -> s) -> Eff effs ()
modify f = get >>= \s -> put $! f s
{-# INLINE modify #-}

evalState :: s -> Eff (State s ': effs) a -> Eff effs a
evalState s0 = handle s0 \case
  Get -> getS
  Put s -> putS s

-- TODO: Eliminate the need for this KnownLength constraint
runState :: forall s a effs. KnownLength effs => s -> Eff (State s ': effs) a -> Eff effs (s, a)
runState s m = evalState s (curry swap <$> m <*> get)

execState :: forall s a effs. KnownLength effs => s -> Eff (State s ': effs) a -> Eff effs s
execState s m = evalState s (m *> get)

data NonDet :: EffectK where
  Empty :: NonDet m a
  Choose :: NonDet m Bool

instance (NonDet :< effs) => Alternative (Eff effs) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send Choose >>= bool b a
  {-# INLINE (<|>) #-}

runNonDetAll :: Alternative f => Eff (NonDet ': effs) a -> Eff effs (f a)
runNonDetAll m = (pure <$> m) & handle () \case
  Empty -> abort empty
  Choose -> shift \k -> liftA2 (<|>) (k True) (k False)
