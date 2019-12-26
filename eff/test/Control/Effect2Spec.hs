module Control.Effect2Spec (spec) where

import Control.Monad
import Test.Hspec

import Control.Effect2

spec :: Spec
spec = do
  describe "local" do
    it "locally modifies the context" do
      let action :: (Reader Integer :< effs) => Eff effs (Integer, Integer, Integer, Integer)
          action = do
            a <- ask @Integer
            (b, c, d) <- local @Integer (+ 5) do
              b <- ask @Integer
              c <- local @Integer (* 3) $ ask @Integer
              d <- ask @Integer
              pure (b, c, d)
            pure (a, b, c, d)

      run (runReader @Integer 10 action) `shouldBe` (10, 15, 45, 15)

  describe "catch" do
    it "applies a function to a thrown exception" do
      let action :: (Error String :< effs) => Eff effs String
          action = throw @String "bang" `catch` \err -> pure $ "caught: " <> err
      run (runError @String action) `shouldBe` Right "caught: bang"

  specify "Error + Reader" do
    let action :: (Error String :< effs, Reader Integer :< effs) => Eff effs ()
        action = do
          n <- ask @Integer
          unless (n > 0) do
            throw $ "value must be positive; given " <> show n

        go :: Integer -> Either String ()
        go n = run $ runReader n $ runError action

    go 42 `shouldBe` Right ()
    go (-10) `shouldBe` Left "value must be positive; given -10"

  describe "Error + State" do
    it "yields the same state regardless of handler order" do
      let action :: (Error () :< effs, State Integer :< effs) => Eff effs ()
          action = do
            modify @Integer (+ 1)
            (modify @Integer (+ 1) *> throw ()) `catch` \() -> pure ()
            modify @Integer (+ 1)

      run (execState @Integer 0 $ runError @() action) `shouldBe` 3
      run (runError @() $ execState @Integer 0 action) `shouldBe` Right 3
