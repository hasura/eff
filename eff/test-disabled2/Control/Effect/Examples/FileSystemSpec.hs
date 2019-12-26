{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Examples.FileSystemSpec where

import Prelude hiding (readFile, writeFile)

import qualified System.IO as IO

import Control.Effect
import Control.Effect.Error
import Control.Effect.State
import Control.Monad.IO.Class
import Data.Functor.Identity
import Test.Hspec

class Monad m => FileSystem m where
  readFile :: FilePath -> m String
  writeFile :: FilePath -> String -> m ()

instance (Monad (t m), Send FileSystem t m) => FileSystem (EffT t m) where
  readFile path = send @FileSystem (readFile path)
  writeFile path contents = send @FileSystem (writeFile path contents)

copyFile :: FileSystem m => FilePath -> FilePath -> m ()
copyFile inPath outPath = do
  contents <- readFile inPath
  writeFile outPath contents

data FileSystemIO
type FileSystemIOT = HandlerT FileSystemIO '[]
type instance Handles FileSystemIOT eff = eff == FileSystem
instance MonadIO m => FileSystem (FileSystemIOT m) where
  readFile path = liftIO $ IO.readFile path
  writeFile path contents = liftIO $ IO.writeFile path contents

runFileSystemIO :: EffT FileSystemIOT m a -> m a
runFileSystemIO = runHandlerT . runEffT

copyFileIO :: MonadIO m => FilePath -> FilePath -> m ()
copyFileIO inPath outPath = runFileSystemIO $ copyFile inPath outPath

-- | A mapping from file paths to file contents.
type VirtualFileSystem = [(FilePath, String)]

data FileSystemPure
type FileSystemPureT = HandlerT FileSystemPure '[StateT VirtualFileSystem]
type instance Handles FileSystemPureT eff = eff == FileSystem
instance Error String m => FileSystem (FileSystemPureT m) where
  readFile path = HandlerT $ do
    fileSystem <- get
    case lookup path fileSystem of
      Just contents -> pure contents
      Nothing       -> throw ("readFile: no such file " <> path)

  writeFile path contents = HandlerT $ do
    fileSystem <- get
    -- add the new file and remove an old file with the same name, if it exists
    put ((path, contents) : filter ((/= path) . fst) fileSystem)

runFileSystemPure :: Monad m => EffT FileSystemPureT m a -> m a
runFileSystemPure = evalState [] . runHandlerT . runEffT

copyFilePure :: Error String m => FilePath -> FilePath -> m ()
copyFilePure inPath outPath = runFileSystemPure $ copyFile inPath outPath

spec :: Spec
spec = describe "copyFile @FileSystemPureT" $ do
  let run :: EffsT '[FileSystemPureT, ExceptT String] Identity a -> Either String a
      run = runIdentity . runError . runFileSystemPure

  it "produces an error if the source does not exist" $ do
    run (copyFile "in.txt" "out.txt") `shouldBe` Left "readFile: no such file in.txt"

  it "copies the file if it exists" $ do
    let go = do
          writeFile "in.txt" "Hello, world!"
          copyFile "in.txt" "out.txt"
          readFile "out.txt"
    run go `shouldBe` Right "Hello, world!"
