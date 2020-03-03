module Control.Effect.NonDet
  ( NonDet(..)
  , Alternative(..)
  , runNonDetAll
  ) where

import Control.Applicative
import Control.Category ((>>>))
import Control.Effect.Base
import Control.Effect.Internal (NonDet(..))

-- Handles a 'NonDet' effect, collecting the results of all branches of the
-- computation. The results are collected __strictly__, which means that /all/
-- effects are evaluated (even if using an 'Alternative' that ignores subsequent
-- results, such as 'Maybe').
--
-- The result is also built using a __left-associated__ sequence of '<|>' calls,
-- which allows the result to be constructed in constant space if an appropriate
-- 'Alternative' instance is used, but can lead to very poor performance for
-- types with inefficient append operations, such as @[]@. Consider using a data
-- structure that supports efficient appends, such as @Data.Sequence.Seq@.
runNonDetAll :: Alternative f => Eff (NonDet ': effs) a -> Eff effs (f a)
runNonDetAll = fmap pure >>> handle \case
  Empty -> abort empty
  Choose -> shift \k -> liftA2 (<|>) (k True) (k False)
