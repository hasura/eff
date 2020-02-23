{-# LANGUAGE NoOverloadedStrings #-}

module Control.Effect.Examples.FileSystemSpec where

import Prelude hiding (readFile, writeFile)

import qualified System.IO as IO

import Control.Effect
import Test.Hspec

-- -----------------------------------------------------------------------------
-- effect definition

data FileSystem :: Effect where
  ReadFile :: FilePath -> FileSystem m String
  WriteFile :: FilePath -> String -> FileSystem m ()

readFile :: FileSystem :< effs => FilePath -> Eff effs String
readFile = send . ReadFile

writeFile :: FileSystem :< effs => FilePath -> String -> Eff effs ()
writeFile a b = send $ WriteFile a b

-- -----------------------------------------------------------------------------
-- IO handler

runFileSystemIO :: IOE :< effs => Eff (FileSystem ': effs) a -> Eff effs a
runFileSystemIO = interpret \case
  ReadFile path -> liftIO $ IO.readFile path
  WriteFile path contents -> liftIO $ IO.writeFile path contents

-- -----------------------------------------------------------------------------
-- pure handler

runFileSystemPure :: Error String :< effs => Eff (FileSystem ': effs) a -> Eff effs a
runFileSystemPure = swizzle
  >>> interpret \case
        ReadFile path -> do
          fileSystem <- get
          case lookup path fileSystem of
            Just contents -> pure contents
            Nothing       -> throw ("readFile: no such file " <> path)
        WriteFile path contents -> do
          fileSystem <- get
          -- add the new file and remove an old file with the same name, if it exists
          put ((path, contents) : filter ((/= path) . fst) fileSystem)
  >>> evalState @[(FilePath, String)] []

-- -----------------------------------------------------------------------------

copyFile :: FileSystem :< effs => FilePath -> FilePath -> Eff effs ()
copyFile inPath outPath = do
  contents <- readFile inPath
  writeFile outPath contents

spec :: Spec
spec = describe "runFileSystemPure" do
  let runPure = run . runError . runFileSystemPure

  it "raises an error if a file does not exist" do
    runPure (copyFile "in.txt" "out.txt") `shouldBe` Left "readFile: no such file in.txt"

  it "copies a file if it exists" do
    let go = do
          writeFile "in.txt" "Hello, world!"
          copyFile "in.txt" "out.txt"
          readFile "out.txt"
    runPure go `shouldBe` Right "Hello, world!"
