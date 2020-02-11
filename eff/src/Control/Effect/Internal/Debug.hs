{-# LANGUAGE CPP #-}

module Control.Effect.Internal.Debug where

import Control.Exception (assert)

#ifdef EFF_DEBUG
import GHC.Stack (HasCallStack)
#else
import Data.Kind (Constraint)
#endif

debugEnabled :: Bool
#ifdef EFF_DEBUG
debugEnabled = True
#else
debugEnabled = False
#endif
{-# INLINE debugEnabled #-}

#ifdef EFF_DEBUG
type DebugCallStack = HasCallStack
#else
type DebugCallStack = () :: Constraint
#endif

assertM :: (DebugCallStack, Applicative m) => Bool -> m ()
assertM b = assert b $ pure ()
{-# INLINE assertM #-}
