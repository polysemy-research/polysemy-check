module CommutativeSpec where

import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck
import Polysemy.State
import Polysemy.Trace


spec :: Spec
spec = do
  prop "State commutes with Trace" $
    prepropCommutative @(State Int) @Trace @TestEffs $
      runTestEffs

  prop "State does not commute with State" $ expectFailure $
    prepropCommutative @(State Int) @(State Int) @TestEffs $
      runTestEffs


type TestEffs = '[State Int, Trace, State Int]

runTestEffs :: Sem TestEffs a -> IO a
runTestEffs =
  pure . run . evalState 0 . fmap snd . runTraceList . subsume

