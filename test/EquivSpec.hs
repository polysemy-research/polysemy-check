{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module EquivSpec where

import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck
import Polysemy.State
import Data.IORef (newIORef)


spec :: Spec
spec = do
  prop "Pure state is equivalent to IO state" $ do
    s0 <- arbitrary
    pure $
      prepropEquivalent @'[State Int] @Int
        (runPureState s0)
        (runIOState s0)
        arbitrary

instance Member (State Int) r => Arbitrary (Sem r Int) where
  arbitrary =
    let terminal = [ pure get, arbitrary ]
     in sized $ \n ->
          case n <= 1 of
            True  -> oneof terminal
            False ->
              oneof $ terminal <>
                [ do
                    k <- arbitrary
                    pure $ get >>= k
                , do
                    s <- arbitrary
                    k <- arbitrary
                    pure $ put s >> k
                ]


runPureState :: Int -> Sem '[State Int] a -> IO a
runPureState s = pure . run . evalState s


runIOState :: Int -> Sem '[State Int, Embed IO] a -> IO (a)
runIOState s sem = do
  ref <- newIORef s
  runM . runStateIORef ref $ sem

