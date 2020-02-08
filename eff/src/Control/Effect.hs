{-# LANGUAGE UndecidableInstances #-}

module Control.Effect
  ( Eff
  , run

  , Effect
  , (:<)
  , lift
  , send

  , handle
  , abort

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

  , Writer(..)
  , tell
  , listen
  , censor
  , runWriter
  , evalWriter
  , execWriter

  , NonDet(..)
  , runNonDetAll

  , type (~>)
  , (&)
  ) where

import Control.Applicative
import Control.Category ((>>>))
import Control.Natural (type (~>))
import Data.Bool (bool)
import Data.Function
import Data.IORef
import Data.Tuple (swap)

import Control.Effect.Internal

data Error e :: Effect where
  Throw :: e -> Error e m a
  Catch :: Eff (Error e ': effs) a -> (e -> Eff effs a) -> Error e (Eff effs) a

throw :: Error e :< effs => e -> Eff effs a
throw = send . Throw
{-# INLINE throw #-}

catch :: Error e :< effs => Eff (Error e ': effs) a -> (e -> Eff effs a) -> Eff effs a
catch a b = send $ Catch a b
{-# INLINE catch #-}

runError :: forall e a effs. Eff (Error e ': effs) a -> Eff effs (Either e a)
runError m = (Right <$> m) & handle \case
  Throw e -> abort @(Error e) $ Left e
  Catch m' f -> either f pure =<< runError m'

data Reader r :: Effect where
  Ask :: Reader r m r
  Local :: (r -> r) -> Eff (Reader r ': effs) a -> Reader r (Eff effs) a

ask :: Reader r :< effs => Eff effs r
ask = send Ask
{-# INLINE ask #-}

local :: Reader r :< effs => (r -> r) -> Eff (Reader r ': effs) ~> Eff effs
local a b = send $ Local a b
{-# INLINE local #-}

runReader :: r -> Eff (Reader r ': effs) ~> Eff effs
runReader r = handle \case
  Ask -> pure r
  Local f m -> let !r' = f r in runReader r' m

data State s :: Effect where
  Get :: State s m s
  Put :: s -> State s m ()

get :: State s :< effs => Eff effs s
get = send Get
{-# INLINE get #-}

put :: State s :< effs => s -> Eff effs ()
put = send . Put
{-# INLINE put #-}

modify :: State s :< effs => (s -> s) -> Eff effs ()
modify f = get >>= put . f
{-# INLINE modify #-}

evalState :: forall s effs. Show s => s -> Eff (State s ': effs) ~> Eff effs
evalState = wind . winder where
  winder !s0 = Winder \pid ts -> do
    putStrLn $ "    State (" ++ show s0 ++ ")"
    ref <- newIORef s0
    let h :: Handler (State s)
        h = Handler (\case
          Get -> Eff \_ _ -> do
            s <- readIORef ref
            putStrLn $ "get: " ++ show s
            pure s
          Put !s -> Eff \_ _ -> do
            putStrLn $ "put: " ++ show s
            writeIORef ref s) pid
    pure (pushTarget h ts, unwinder ref)
  unwinder ref = Unwinder pure (pure ()) (winder <$> readIORef ref)

runState :: forall s a effs. Show s => s -> Eff (State s ': effs) a -> Eff effs (s, a)
runState s m = evalState s (curry swap <$> m <*> get)

execState :: forall s a effs. Show s => s -> Eff (State s ': effs) a -> Eff effs s
execState s m = evalState s (m *> get)

data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: Eff (Writer w ': effs) a -> Writer w (Eff effs) (w, a)
  Censor :: (w -> w) -> Eff (Writer w ': effs) a -> Writer w (Eff effs) a

tell :: Writer w :< effs => w -> Eff effs ()
tell = send . Tell
{-# INLINE tell #-}

listen :: Writer w :< effs => Eff (Writer w ': effs) a -> Eff effs (w, a)
listen = send . Listen
{-# INLINE listen #-}

censor :: Writer w :< effs => (w -> w) -> Eff (Writer w ': effs) a -> Eff effs a
censor a b = send $ Censor a b
{-# INLINE censor #-}

runWriter :: forall w effs a. (Monoid w, Show w) => Eff (Writer w ': effs) a -> Eff effs (w, a)
runWriter = swizzle
  >>> handle \case
        Tell w -> liftH @(Writer w) $ tellS w
        Listen m -> runListen m
        Censor f m -> runCensor f m
  >>> runState @w mempty
  where
    tellS :: State w :< effs' => w -> Eff effs' ()
    tellS w = get >>= \ws -> put $! (ws <> w)

    runListen :: forall effs1 i effs2 b. Handling (Writer w) effs1 i effs2
              => Eff (Writer w ': effs2) b -> Eff effs2 (w, b)
    runListen = swizzle
      >>> handle @(Writer w) \case
            Tell w -> liftH @(Writer w) do
              tellS w
              lift @effs2 $ liftH @(Writer w) $ tell w
            Listen m -> runListen m
            Censor f m -> runCensor f m
      >>> runState @w mempty

    runCensor :: forall effs1 i effs2. Handling (Writer w) effs1 i effs2
              => (w -> w) -> Eff (Writer w ': effs2) ~> Eff effs2
    runCensor f = handle @(Writer w) \case
      Tell w -> liftH @(Writer w) $ lift1 $ liftH @(Writer w) (tell $! f w)
      Listen m -> runListen m
      Censor g m -> runCensor g m

evalWriter :: forall w effs. (Monoid w, Show w) => Eff (Writer w ': effs) ~> Eff effs
evalWriter = fmap snd . runWriter

execWriter :: forall w effs a. (Monoid w, Show w) => Eff (Writer w ': effs) a -> Eff effs w
execWriter = fmap fst . runWriter

data NonDet :: Effect where
  Empty :: NonDet m a
  Choose :: NonDet m Bool

instance NonDet :< effs => Alternative (Eff effs) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send Choose >>= bool b a
  {-# INLINE (<|>) #-}

runNonDetAll :: Alternative f => Eff (NonDet ': effs) a -> Eff effs (f a)
runNonDetAll m = (pure <$> m) & handle \case
  Empty -> abort @NonDet empty
  Choose -> shift @NonDet \k -> liftA2 (<|>) (k True) (k False)
