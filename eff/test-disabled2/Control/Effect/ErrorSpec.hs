module Control.Effect.ErrorSpec (spec) where

import Control.Effect.Error
import Control.Effect.State
import Data.Functor.Identity
import Data.List
import Test.Hspec

spec :: Spec
spec = do
  let inc :: State Integer m => m ()
      inc = modify @Integer (+1)

  describe "throw" $ do
    it "aborts the current computation" $ do
      let m :: (Error String m, State Integer m) => m ()
          m = inc *> throw @String "bang" *> inc

      runIdentity (runError @String (runState @Integer 0 m)) `shouldBe` Left "bang"
      runIdentity (runState @Integer 0 (runError @String m)) `shouldBe` (1, Left "bang")

  describe "catch" $ do
    it "resumes the computation from the location of catch" $ do
      let m :: (Error String m, State Integer m) => m ()
          m = do
            inc
            (inc *> throw @String "bang" *> inc)
              `catch` \(str :: String) -> modify @Integer (+ genericLength str)
            inc

      runIdentity (runError @String (runState @Integer 0 m)) `shouldBe` Right (7, ())
      runIdentity (runState @Integer 0 (runError @String m)) `shouldBe` (7, Right ())
