{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wno-orphans             #-}
{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}

module EquivSpec where

import Data.IORef (newIORef, readIORef)
import Data.Proxy (Proxy)
import Polysemy
import Polysemy.Check
import Polysemy.State
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck


spec :: Spec
spec = do
  prop "Pure state is equivalent to IO state" $ do
    s0 <- arbitrary
    pure $
      prepropEquivalent @'[State Int] @Int
        (runPureState s0)
        (runIOState s0)
        $ \(_ :: Proxy r) -> do
            SomeAction e1 <- arbitraryAction @(State Int) @r
            SomeAction e2 <- arbitraryAction @(State Int) @r
            e3 <- arbitraryActionOfType @(State Int) @Int @r
            pure $ send e1 >> send e2 >> send e3


runPureState :: Int -> Sem '[State Int] a -> IO (Int, a)
runPureState s = pure . run . runState s


runIOState :: Int -> Sem '[State Int, Embed IO] a -> IO (Int, a)
runIOState s sem = do
  ref <- newIORef s
  a <- runM . runStateIORef ref $ sem
  r <- readIORef ref
  pure (r, a)

