module Control.Effect.WriterSpec (spec) where

import Control.Effect.Error
import Control.Effect.Writer
import Data.Functor
import Data.Functor.Identity
import Test.Hspec

spec :: Spec
spec = do
  let tellStr :: Writer [String] m => String -> m ()
      tellStr s = tell [s]

  describe "tell" $ do
    it "adds a message to the log" $
      runIdentity (runWriter @[String] (tellStr "a" *> tellStr "b")) `shouldBe` (["a", "b"], ())

  describe "listen" $ do
    it "accumulates results in a local scope" $ do
      let m = tellStr "a" *> listen @[String] (tellStr "b" *> tellStr "c") <* tellStr "d"
      runIdentity (runWriter @[String] m) `shouldBe` (["a", "b", "c", "d"], (["b", "c"], ()))

    context "within a short-circuited context" $
      it "does not prevent writes to the global log" $ do
        let m = do
              tellStr "a"
              void (listen @[String] (tellStr "b" *> throw () *> tellStr "c")) `catch` pure
              tellStr "d"
        runIdentity (runWriter @[String] $ runError @() m) `shouldBe` (["a", "b", "d"], Right ())
