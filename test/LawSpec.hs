{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}

module LawSpec where

import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck
import Polysemy.State
import Data.IORef (newIORef, readIORef)


spec :: Spec
spec = do
  describe "pure state" $ do
    prop "put >> put = put" $ do
      s <- arbitrary
      pure $ putPutLaw $ runPureState s
    prop "get >>= put = pure ()" $ do
      s <- arbitrary
      pure $ getPutLaw $ runPureState s
    prop "put >> get = put >> pure" $ do
      s <- arbitrary
      pure $ putGetLaw $ runPureState s

  describe "io state" $ do
    prop "put >> put = put" $ do
      s <- arbitrary
      pure $ putPutLaw $ runIOState s
    prop "get >>= put = pure ()" $ do
      s <- arbitrary
      pure $ getPutLaw $ runIOState s
    prop "put >> get = put >> pure" $ do
      s <- arbitrary
      pure $ putGetLaw $ runIOState s


putPutLaw
    :: (Arbitrary s, Member (State s) r, Eq x, Show x)
    => (Sem r s -> IO x)
    -> Property
putPutLaw = prepropLaw $ do
  s1 <- arbitrary
  s2 <- arbitrary
  pure
    ( do
        put s1
        put s2
        get
    , do
        put s2
        get
    )


getPutLaw
    :: (Arbitrary s, Member (State s) r, Eq x, Show x)
    => (Sem r () -> IO x)
    -> Property
getPutLaw = prepropLaw $ do
  pure
    ( get >>= put
    , pure ()
    )


putGetLaw
    :: (Arbitrary s, Member (State s) r, Eq x, Show x)
    => (Sem r s -> IO x)
    -> Property
putGetLaw = prepropLaw $ do
  s <- arbitrary
  pure
    ( do
        put s
        get
    , do
        put s
        pure s
    )


runPureState :: Int -> Sem '[State Int] a -> IO (Int, a)
runPureState s = pure . run . runState s


runIOState :: Int -> Sem '[State Int, Embed IO] a -> IO (Int, a)
runIOState s sem = do
  ref <- newIORef s
  a <- runM . runStateIORef ref $ sem
  r <- readIORef ref
  pure (r, a)

