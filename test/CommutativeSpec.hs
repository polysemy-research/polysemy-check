module CommutativeSpec where

import Data.Functor.Compose
import Polysemy
import Polysemy.Check
import Polysemy.Error (Error, runError)
import Polysemy.State
import Polysemy.Trace
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck


spec :: Spec
spec = do
  prop "State commutes with Trace" $
    prepropCommutative @(State Int) @Trace @TestEffs $
      runTestEffs

  prop "State does not commute with itself" $ expectFailure $
    prepropCommutative @(State Int) @(State Int) @TestEffs $
      runTestEffs

  prop "Error does not commute with State (really: we can do Arbitrary stuff on Error)" $ expectFailure $
    prepropCommutative @(Error Int) @(State Int) @[Error Int, State Int] $
      pure . Compose . run . runState 0 . runError


type TestEffs = '[State Int, Trace, State Int]

runTestEffs :: Sem TestEffs a -> IO (Compose ((,) Int) ((,) [String]) a)
runTestEffs =
  pure . Compose . run . runState 0 . runTraceList . subsume

