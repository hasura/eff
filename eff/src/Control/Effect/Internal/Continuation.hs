{-# LANGUAGE MagicHash #-}

module Control.Effect.Internal.Continuation
  ( Continuation(..)
  , reset
  , shift
  , applyContinuation
  ) where

import Control.Monad.Primitive
import GHC.Exts (Continuation#, reset#, shift#, applyContinuation#)

data Continuation a b = Continuation# (Continuation# a b)

reset :: IO a -> IO a
reset m = primitive (reset# (internal m))
{-# INLINE reset #-}

shift :: (Continuation a b -> IO b) -> IO a
shift f = primitive (shift# \k -> internal (f (Continuation# k)))
{-# INLINE shift #-}

applyContinuation :: Continuation a b -> IO a -> IO b
applyContinuation (Continuation# k) m = primitive (applyContinuation# k (internal m))
{-# INLINE applyContinuation #-}
