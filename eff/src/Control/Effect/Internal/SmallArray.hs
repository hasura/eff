{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module Control.Effect.Internal.SmallArray
  ( SmallArray(..)
  , SmallMutableArray(..)
  , newSmallArray
  , P.runSmallArray
  , P.unsafeFreezeSmallArray
  , P.unsafeThawSmallArray
  , sizeofSmallArray
  , sizeofSmallMutableArray
  , indexSmallArray
  , readSmallArray
  , writeSmallArray
  , copySmallArray
  , copySmallMutableArray
  , cloneSmallMutableArray
  ) where

import qualified Data.Primitive.SmallArray as P

import Control.Exception (assert)
import Control.Monad.Primitive
import Data.Primitive.SmallArray (SmallArray(..), SmallMutableArray(..))
import GHC.Exts (Int(..), indexSmallArray#)

import Control.Effect.Internal.Debug

newSmallArray :: (DebugCallStack, PrimMonad m) => Int -> a -> m (SmallMutableArray (PrimState m) a)
newSmallArray len x = assert (len >= 0) $ P.newSmallArray len x
{-# INLINE newSmallArray #-}

sizeofSmallArray :: DebugCallStack => SmallArray a -> Int
sizeofSmallArray arr = let len = P.sizeofSmallArray arr in assert (len >= 0) len
{-# INLINE sizeofSmallArray #-}

sizeofSmallMutableArray :: DebugCallStack => SmallMutableArray s a -> Int
sizeofSmallMutableArray arr = let len = P.sizeofSmallMutableArray arr in assert (len >= 0) len
{-# INLINE sizeofSmallMutableArray #-}

indexSmallArray :: DebugCallStack => SmallArray a -> Int -> (# a #)
indexSmallArray arr idx =
  -- We have to put the assertions in a pointless strict binding because `assert` can’t accept an
  -- unlifted argument.
  let !() = assert (idx >= 0) $ assert (idx < sizeofSmallArray arr) ()
      !(SmallArray arr#) = arr
      !(I# idx#) = idx
  in indexSmallArray# arr# idx#
{-# INLINE indexSmallArray #-}

readSmallArray :: (DebugCallStack, PrimMonad m) => SmallMutableArray (PrimState m) a -> Int -> m a
readSmallArray arr idx =
  assert (idx >= 0) $ assert (idx < sizeofSmallMutableArray arr) $ P.readSmallArray arr idx
{-# INLINE readSmallArray #-}

writeSmallArray
  :: (DebugCallStack, PrimMonad m) => SmallMutableArray (PrimState m) a -> Int -> a -> m ()
writeSmallArray arr idx x = do
  assertM $ idx >= 0
  assertM $ idx < sizeofSmallMutableArray arr
  P.writeSmallArray arr idx x
{-# INLINE writeSmallArray #-}

copySmallArray
  :: (DebugCallStack, PrimMonad m)
  => SmallMutableArray (PrimState m) a -> Int -> SmallArray a -> Int -> Int -> m ()
copySmallArray dst idx_dst src idx_src len = do
  assertM $ len >= 0
  assertM $ idx_dst >= 0
  assertM $ idx_dst + len <= sizeofSmallMutableArray dst
  assertM $ idx_src >= 0
  assertM $ idx_src + len <= sizeofSmallArray src
  P.copySmallArray dst idx_dst src idx_src len
{-# INLINE copySmallArray #-}

copySmallMutableArray
  :: (DebugCallStack, PrimMonad m)
  => SmallMutableArray (PrimState m) a -> Int -> SmallMutableArray (PrimState m) a -> Int -> Int -> m ()
copySmallMutableArray dst idx_dst src idx_src len = do
  assertM $ len >= 0
  assertM $ idx_dst >= 0
  assertM $ idx_dst + len <= sizeofSmallMutableArray dst
  assertM $ idx_src >= 0
  assertM $ idx_src + len <= sizeofSmallMutableArray src
  P.copySmallMutableArray dst idx_dst src idx_src len
{-# INLINE copySmallMutableArray #-}

cloneSmallMutableArray
  :: (DebugCallStack, PrimMonad m)
  => SmallMutableArray (PrimState m) a -> Int -> Int -> m (SmallMutableArray (PrimState m) a)
cloneSmallMutableArray src idx len = do
  assertM $ len >= 0
  assertM $ idx >= 0
  assertM $ idx + len <= sizeofSmallMutableArray src
  P.cloneSmallMutableArray src idx len
{-# INLINE cloneSmallMutableArray #-}
