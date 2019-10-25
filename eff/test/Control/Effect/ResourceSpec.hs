module Control.Effect.ResourceSpec (spec) where

import Control.Effect
import Control.Effect.Error
import Control.Effect.Resource
import Control.Effect.Writer
import Control.Exception (ErrorCall(..), throwIO, try)
import Control.Monad.IO.Class
import Data.IORef
import Data.Functor
import Test.Hspec

spec :: Spec
spec = do
  let run :: EffsT '[ExceptT String, WriterT [String]] IO a
          -> IO (Either ErrorCall ([String], Either String a))
      run = try . runWriter . runError

  describe "bracket_" $ do
    it "runs a cleanup action on success" $ do
      result <- run $ bracket_
        (tell @[String] ["setup"])
        (tell @[String] ["teardown"])
        (tell @[String] ["act"])
      result `shouldBe` Right (["setup", "act", "teardown"], Right ())

    it "runs a cleanup action on IO exception" $ do
      didCleanUp <- newIORef False
      result <- run $ bracket_
        (pure ())
        (liftIO $ writeIORef didCleanUp True)
        (void . liftIO . throwIO $ ErrorCall "bang")
      readIORef didCleanUp `shouldReturn` True
      result `shouldBe` Left (ErrorCall "bang")

    it "runs a cleanup action on Error exceptions" $ do
      result <- run $ bracket_
        (tell @[String] ["setup"])
        (tell @[String] ["teardown"])
        (tell @[String] ["act1"] *> throw @String "bang" *> tell @[String] ["act2"])
      result `shouldBe` Right (["setup", "act1", "teardown"], Left "bang")

  describe "bracketOnError_" $ do
    it "skips the cleanup action on success" $ do
      result <- run $ bracketOnError_
        (tell @[String] ["setup"])
        (tell @[String] ["teardown"])
        (tell @[String] ["act"])
      result `shouldBe` Right (["setup", "act"], Right ())

    it "runs a cleanup action on IO exception" $ do
      didCleanUp <- newIORef False
      result <- run $ bracketOnError_
        (pure ())
        (liftIO $ writeIORef didCleanUp True)
        (void . liftIO . throwIO $ ErrorCall "bang")
      readIORef didCleanUp `shouldReturn` True
      result `shouldBe` Left (ErrorCall "bang")

    it "runs a cleanup action on Error exceptions" $ do
      result <- run $ bracketOnError_
        (tell @[String] ["setup"])
        (tell @[String] ["teardown"])
        (tell @[String] ["act1"] *> throw @String "bang" *> tell @[String] ["act2"])
      result `shouldBe` Right (["setup", "act1", "teardown"], Left "bang")
