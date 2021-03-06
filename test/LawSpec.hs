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
      pure $ putPutLaw Nothing $ runPureState s
    prop "get >>= put = pure ()" $ do
      s <- arbitrary
      pure $ getPutLaw Nothing $ runPureState s
    prop "put >> get = put >> pure" $ do
      s <- arbitrary
      pure $ putGetLaw Nothing $ runPureState s

  describe "io state" $ do
    prop "put >> put = put" $ do
      s <- arbitrary
      pure $ putPutLaw Nothing $ runIOState s
    prop "get >>= put = pure ()" $ do
      s <- arbitrary
      pure $ getPutLaw Nothing $ runIOState s
    prop "put >> get = put >> pure" $ do
      s <- arbitrary
      pure $ putGetLaw Nothing $ runIOState s


type LawConstraints f effs s r =
       ( Arbitrary s
       , Members effs r
       , Eq s
       , Show s
       , ArbitraryEff effs r
       , f ~ (,) s
       , effs ~ '[State s]
       )


putPutLaw
    :: forall s r res effs f
     . ( res ~ ()
       , LawConstraints f effs s r
       )
    => Maybe (f res -> String)
    -> (forall a. Sem r (res, a) -> IO (f (res, a)))
    -> Property
putPutLaw = prepropLaw @effs $ do
  s1 <- arbitrary
  s2 <- arbitrary
  pure $ simpleLaw
    ( do
        put s1
        put s2)
    ( do
        put s2)


getPutLaw
    :: forall s r res effs f
     . ( res ~ ()
       , LawConstraints f effs s r
       )
    => Maybe (f res -> String)
    -> (forall a. Sem r (res, a) -> IO (f (res, a)))
    -> Property
getPutLaw = prepropLaw @effs $ do
  pure $ simpleLaw
    (get >>= put)
    (pure ())


putGetLaw
    :: forall s r res effs f
     . ( res ~ s
       , LawConstraints f effs s r
       )
    => Maybe (f res -> String)
    -> (forall a. Sem r (res, a) -> IO (f (res, a)))
    -> Property
putGetLaw = prepropLaw @effs $ do
  s <- arbitrary
  pure $ simpleLaw
    ( do
        put s
        get)
    ( do
        put s
        pure s)


runPureState :: Int -> Sem '[State Int] a -> IO (Int, a)
runPureState s = pure . run . runState s


runIOState :: Int -> Sem '[State Int, Embed IO] a -> IO (Int, a)
runIOState s sem = do
  ref <- newIORef s
  a <- runM . runStateIORef ref $ sem
  r <- readIORef ref
  pure (r, a)

