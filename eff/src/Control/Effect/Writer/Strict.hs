module Control.Effect.Writer.Strict
  ( module Control.Effect.Writer
  , runWriter
  , evalWriter
  , execWriter
  ) where

import Control.Category ((>>>))
import Control.Effect.Base
import Control.Effect.State.Strict
import Control.Effect.Writer
import Data.Function

-- | Handles a @'Writer'@ effect, strictly accumulating the monoidal state.
--
-- Note that the state will be accumulated via __left-associated__ uses of '<>'.
-- This is necessary to be strict, but it can be catastrophically slow on
-- certain monoids, most notably @[]@. To avoid pathological performance, use a
-- data structure that supports efficient appends, such as @Data.Sequence.Seq@,
-- or use 'Data.Semigroup.Dual' to flip the argument order of '<>' (but beware
-- that this will cause the elements to be accumulated in reverse order).
runWriter :: Monoid w => Eff (Writer w ': effs) a -> Eff effs (w, a)
runWriter (m0 :: Eff (Writer w ': effs) a) = lift m0
  & handle \case
      Tell w -> liftH $ tellS w
      Listen m -> locally $ runListen m
      Censor f m -> locally $ runCensor f m
  & runState mempty
  where
    tellS :: State w :< effs' => w -> Eff effs' ()
    tellS w = get >>= \ws -> put $! (ws <> w)

    runListen :: Writer w :< effs' => Eff (Writer w ': effs') b -> Eff effs' (w, b)
    runListen = lift
      >>> handle \case
            Tell w -> liftH do
              tellS w
              lift1 $ tell w
            Listen m -> locally $ runListen m
            Censor f m -> locally $ runCensor f m
      >>> runState mempty

    runCensor :: Writer w :< effs' => (w -> w) -> Eff (Writer w ': effs') b -> Eff effs' b
    runCensor f = handle \case
      Tell w -> liftH $ lift1 (tell $! f w)
      Listen m -> locally $ runListen m
      Censor g m -> locally $ runCensor g m

evalWriter :: Monoid w => Eff (Writer w ': effs) a -> Eff effs a
evalWriter = fmap snd . runWriter

execWriter :: Monoid w => Eff (Writer w ': effs) a -> Eff effs w
execWriter = fmap fst . runWriter
