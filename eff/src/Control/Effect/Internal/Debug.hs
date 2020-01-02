{-# LANGUAGE CPP #-}

module Control.Effect.Internal.Debug where

import Control.Exception (assert)

debugEnabled :: Bool
#ifdef EFF_DEBUG
debugEnabled = True
#else
debugEnabled = False
#endif
{-# INLINE debugEnabled #-}

assertM :: Applicative m => Bool -> m ()
assertM b = assert b $ pure ()
{-# INLINE assertM #-}
