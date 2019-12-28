module Control.EffectSpec (spec) where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Test.Hspec

import Control.Effect

spec :: Spec
spec = do
  describe "local" do
    it "locally modifies the context" do
      let action :: Reader Integer :< effs => Eff effs (Integer, Integer, Integer, Integer)
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
      let action :: Error String :< effs => Eff effs String
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

  -- describe "Error + State" do
  --   it "yields the same state regardless of handler order" do
  --     let action :: (Error () :< effs, State Integer :< effs) => Eff effs ()
  --         action = do
  --           modify @Integer (+ 1)
  --           (modify @Integer (+ 1) *> throw ()) `catch` \() -> pure ()
  --           modify @Integer (+ 1)
  --
  --     run (execState @Integer 0 $ runError @() action) `shouldBe` 3
  --     run (runError @() $ execState @Integer 0 action) `shouldBe` Right 3
  --
  -- describe "NonDet" do
  --   describe "runNonDetAll" do
  --     it "collects the results of all branches" do
  --       let action :: NonDet :< effs => Eff effs (Integer, Integer)
  --           action = do
  --             a <- asum $ map pure [1, 2, 3]
  --             b <- asum $ map pure [4, 5, 6]
  --             pure (a, b)
  --       run (runNonDetAll action) `shouldBe` [(a, b) | a <- [1, 2, 3], b <- [4, 5, 6]]
  --
  --     specify "choice + catch with exit" do
  --       let results = run $ runError @() $ runNonDetAll do
  --             b <- (pure True <|> throw ()) `catch` \() -> pure False
  --             pure $ not b
  --       results `shouldBe` Right [False, True]
  --
  --     specify "choice + catch with early exit" do
  --       let results = run $ runError @() $ runNonDetAll do
  --             b <- (throw () <|> pure True) `catch` \() -> pure False
  --             pure $ not b
  --       results `shouldBe` Right [True, False]
