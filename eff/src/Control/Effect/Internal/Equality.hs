{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}

module Control.Effect.Internal.Equality
  ( type (~#)(Refl#)
  , unsafeRefl#
  ) where

import Data.Type.Equality
import GHC.Exts (RuntimeRep(..), TYPE, Void#, void#)
import Unsafe.Coerce (unsafeCoerce)

type (~#) :: k -> k -> TYPE ('TupleRep '[])
newtype a ~# b = UnsafeRefl# Void#

pattern Refl# :: () => a ~ b => a ~# b
pattern Refl# <- (boxEq# -> Refl) where
  Refl# = UnsafeRefl# void#
{-# COMPLETE Refl# #-}

boxEq# :: a ~# b -> a :~: b
boxEq# _ = unsafeCoerce Refl
{-# INLINE boxEq# #-}

unsafeRefl# :: Void# -> a ~# b
unsafeRefl# = UnsafeRefl#
{-# INLINE unsafeRefl# #-}
