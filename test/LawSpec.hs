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
    :: forall s r
     . ( Arbitrary s
       , Member (State s) r
       , Eq s
       , Show s
       , ArbitraryEff '[State s] r
       )
    => (forall a. Sem r ((), a) -> IO (s, ((), a)))
    -> Property
putPutLaw = prepropLaw @'[State s] $ do
  s1 <- arbitrary
  s2 <- arbitrary
  pure
    ( do
        put s1
        put s2
    , do
        put s2
    )


getPutLaw
    :: forall s r
     . ( Arbitrary s
       , Member (State s) r
       , Eq s
       , Show s
       , ArbitraryEff '[State s] r
       )
    => (forall a. Sem r ((), a) -> IO (s, ((), a)))
    -> Property
getPutLaw = prepropLaw @'[State s] $ do
  pure
    ( get >>= put
    , pure ()
    )


putGetLaw
    :: forall s r
     . ( Arbitrary s
       , Member (State s) r
       , Eq s
       , Show s
       , ArbitraryEff '[State s] r
       )
    => (forall a. Sem r (s, a) -> IO (s, (s, a)))
    -> Property
putGetLaw = prepropLaw @'[State s] $ do
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

