module Control.Effect.Internal.PrimArray
  ( PrimArray
  , MutablePrimArray
  , newPrimArray
  , runPrimArray
  , sizeofPrimArray
  , getSizeofMutablePrimArray
  , indexPrimArray
  , writePrimArray
  , copyPrimArray
  , clonePrimArray
  ) where

import qualified Data.Primitive.PrimArray as P

import Control.Exception (assert)
import Control.Monad
import Control.Monad.Primitive
import Control.Monad.ST
import Data.Primitive.Types
import Data.Primitive.PrimArray (PrimArray, MutablePrimArray)

import Control.Effect.Internal.Debug

newPrimArray :: (DebugCallStack, Prim a, PrimMonad m) => Int -> m (MutablePrimArray (PrimState m) a)
newPrimArray len = assert (len >= 0) $ P.newPrimArray len
{-# INLINE newPrimArray #-}

runPrimArray :: (forall s. ST s (MutablePrimArray s a)) -> PrimArray a
runPrimArray m = runST (P.unsafeFreezePrimArray =<< m)
{-# INLINE runPrimArray #-}

sizeofPrimArray :: (DebugCallStack, Prim a) => PrimArray a -> Int
sizeofPrimArray arr = let len = P.sizeofPrimArray arr in assert (len >= 0) len
{-# INLINE sizeofPrimArray #-}

getSizeofMutablePrimArray
  :: (DebugCallStack, Prim a, PrimMonad m) => MutablePrimArray (PrimState m) a -> m Int
getSizeofMutablePrimArray arr = do
  len <- P.getSizeofMutablePrimArray arr
  assertM $ len >= 0
  pure len
{-# INLINE getSizeofMutablePrimArray #-}

indexPrimArray :: (DebugCallStack, Prim a) => PrimArray a -> Int -> a
indexPrimArray arr idx =
  assert (idx >= 0) $ assert (idx < sizeofPrimArray arr) $ P.indexPrimArray arr idx
{-# INLINE indexPrimArray #-}

writePrimArray
  :: (DebugCallStack, Prim a, PrimMonad m) => MutablePrimArray (PrimState m) a -> Int -> a -> m ()
writePrimArray arr idx x = do
  when debugEnabled do
    assertM $ idx >= 0
    len <- getSizeofMutablePrimArray arr
    assertM $ idx < len
  P.writePrimArray arr idx x
{-# INLINE writePrimArray #-}

clonePrimArray :: (DebugCallStack, Prim a) => PrimArray a -> Int -> Int -> PrimArray a
clonePrimArray src idx len = runPrimArray do
  dst <- newPrimArray len
  copyPrimArray dst 0 src idx len
  pure dst
{-# INLINE clonePrimArray #-}

copyPrimArray
  :: (DebugCallStack, Prim a, PrimMonad m)
  => MutablePrimArray (PrimState m) a -> Int -> PrimArray a -> Int -> Int -> m ()
copyPrimArray dst idx_dst src idx_src len = do
  when debugEnabled do
    assertM $ len >= 0
    assertM $ idx_dst >= 0
    dst_len <- getSizeofMutablePrimArray dst
    assertM $ idx_dst + len < dst_len
    assertM $ idx_src >= 0
    assertM $ idx_src + len < sizeofPrimArray src
  P.copyPrimArray dst idx_dst src idx_src len
{-# INLINE copyPrimArray #-}
