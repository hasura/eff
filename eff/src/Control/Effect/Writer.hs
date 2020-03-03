module Control.Effect.Writer
  ( Writer(..)
  , tell
  , listen
  , censor
  ) where

import Control.Effect.Base

-- | The @'Writer' w@ effect allows the accumulation of monoidal values of type
-- @w@.
--
-- Instances should obey the following laws:
--
--   * @'tell' /x/ '*>' 'tell' /y/@ ≡ @'tell' (/x/ '<>' /y/)@
--   * @'listen' ('tell' /x/)@ ≡ @(/x/,) '<$>' 'tell' /x/@
--   * @'censor' /f/ ('tell' /x/)@ ≡ @'tell' (/f/ /x/)@
data Writer w :: Effect where
  Tell :: w -> Writer w m ()
  Listen :: Eff (Writer w ': effs) a -> Writer w (Eff effs) (w, a)
  Censor :: (w -> w) -> Eff (Writer w ': effs) a -> Writer w (Eff effs) a

-- | Appends the given value to the current output.
tell :: Writer w :< effs => w -> Eff effs ()
tell = send . Tell

-- | Executes the given action and includes its output in the result.
listen :: Writer w :< effs => Eff (Writer w ': effs) a -> Eff effs (w, a)
listen = send . Listen

-- | Executes the given action and modifies its output by applying the given
-- function.
censor :: Writer w :< effs => (w -> w) -> Eff (Writer w ': effs) a -> Eff effs a
censor a b = send $ Censor a b
