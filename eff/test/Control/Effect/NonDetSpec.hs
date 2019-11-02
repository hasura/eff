module Control.Effect.NonDetSpec (spec) where

import Control.Applicative
import Control.Effect
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.Writer
import Data.Functor.Identity
import Test.Hspec

spec :: Spec
spec = describe "interaction with scoped effects" $ do
  specify "choice inside scoped operations" $ do
    let results = runIdentity $ runReader True $ runNonDetAll $
          ask <|> local not (ask <|> ask) <|> ask
    results `shouldBe` [True, False, False, True]

  specify "lazy fold with scoped operations" $ do
    let takeNonDet :: forall m a. Monad m => Integer -> EffT NonDetT m a -> m [a]
        takeNonDet n xs0 =
          let next :: Integer -> m (Integer -> m [a]) -> m [a]
              next m xs
                | m < n     = xs >>= ($ m)
                | otherwise = pure []
              go x xs = pure $ \m -> (x :) <$> next (m + 1) xs
          in next 0 $ foldrNonDet go (pure $ \_ -> pure []) xs0

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
