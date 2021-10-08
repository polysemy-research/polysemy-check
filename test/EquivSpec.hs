{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wno-orphans             #-}
{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}

module EquivSpec where

import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck
import Polysemy.State
import Data.IORef (newIORef)
import Unsafe.Coerce (unsafeCoerce)


spec :: Spec
spec = do
  prop "Pure state is equivalent to IO state" $ do
    s0 <- arbitrary
    pure $
      prepropEquivalent @'[State Int] @Int
        (runPureState s0)
        (runIOState s0)
        $ ((do
            SomeAction e1 <- arbitraryAction @(State Int) @r
            SomeAction e2 <- arbitraryAction @(State Int) @r
            SomeAction e3 <- arbitraryAction @(State Int) @r
            -- TODO(sandy): e3 has an existential type! GHC doesn't care, but
            -- AFAIK, thereis no syntax to return this type, since it doesn't
            -- exist when we bind 'a' below.
            pure $ send e1 >> send e2 >> unsafeCoerce (send e3)
           ) :: forall r a. Member (State Int) r => Gen (Sem r a))


runPureState :: Int -> Sem '[State Int] a -> IO a
runPureState s = pure . run . evalState s


runIOState :: Int -> Sem '[State Int, Embed IO] a -> IO (a)
runIOState s sem = do
  ref <- newIORef s
  runM . runStateIORef ref $ sem

