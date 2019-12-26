module Control.Effect.NonDetSpec (spec) where

import qualified Control.Effect.NonDet as NonDet

import Control.Applicative
import Control.Effect
import Control.Effect.Error
import Control.Effect.NonDet (NonDetT)
import Control.Effect.Reader
import Control.Effect.Writer
import Data.Monoid (Sum(..))
import Data.Functor
import Data.Functor.Identity
import Test.Hspec

spec :: Spec
spec = describe "interaction with scoped effects" $ do
  specify "choice inside scoped operations" $ do
    let results = runIdentity $ runReader True $ NonDet.runAll $
          ask <|> local not (ask <|> ask) <|> ask
    results `shouldBe` [True, False, False, True]

  specify "choice inside scoped operations with multiple continuations" $ do
    let results = runIdentity $ runError @() $ NonDet.runAll $ do
          b <- (pure True <|> throw ()) `catch` \() -> pure False
          pure $ not b
    results `shouldBe` Right [False, True]

  specify "choice inside scoped operations with early exit" $ do
    let results = runIdentity $ runError @() $ NonDet.runAll $ do
          b <- (throw () <|> pure True) `catch` \() -> pure False
          pure $ not b
    results `shouldBe` Right [True, False]

  describe "listen over (<|>)" $ do
    let go :: (Alternative m, Writer (Sum Integer) m) => m ((Sum Integer), Bool)
        go = listen $ do
          let add = tell . Sum @Integer
          add 1 $> True <|> add 2 $> False

    context "Writer has local semantics relative to Alternative" $ do
      it "returns output from each choice" $ do
        let results = runIdentity $ NonDet.runAll $ runWriter @(Sum Integer) go
        results `shouldBe` [(Sum 1, (Sum 1, True)), (Sum 2, (Sum 2, False))]

    context "Writer has global semantics relative to Alternative" $ do
      it "returns output from each choice" $ do
        let results = runIdentity $ runWriter @(Sum Integer) $ NonDet.runAll go
        results `shouldBe` (Sum 3, [(Sum 1, True), (Sum 2, False)])

  specify "lazy fold with scoped operations" $ do
    let takeNonDet :: forall m a. Monad m => Integer -> EffT NonDetT m a -> m [a]
        takeNonDet n =
          let next :: Integer -> m (Integer -> m [a]) -> m [a]
              next m xs
                | m < n     = xs >>= ($ m)
                | otherwise = pure []
              go x xs = pure $ \m -> (x :) <$> next (m + 1) xs
          in next 0 . NonDet.foldr go (pure $ \_ -> pure [])

        results = runIdentity $ runWriter @[String] $ runReader True $ takeNonDet 6 $ do
          x <- ask <|> local not
            ((tell @[String] ["three"] *> ask) <|> (tell @[String] ["four"] *> ask))
          tell @[String] ["one"]
          y <- local not (ask <|> (tell @[String] ["two"] *> ask)) <|> ask
          pure (x, y)

    results `shouldBe`
      ( [ "one", "two", "three", "one", "two" ]
      , [ (True, False), (True, False), (True, True)
        , (False, False), (False, False), (False, True)
        ] )
