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
import Polysemy.Input
import Polysemy.Output
import Data.Foldable (traverse_)


spec :: Spec
spec = do
  prop "State commutes with Trace" $
    prepropCommutative @'[State Int] @'[Trace] @TestEffs $
      runTestEffs

  prop "State does not commute with itself" $ expectFailure $
    prepropCommutative @'[State Int] @'[State Int] @TestEffs $
      runTestEffs

  prop "Error does not commute with State (really: we can do Arbitrary stuff on Error)" $ expectFailure $
    prepropCommutative @'[Error Int] @'[State Int] @'[Error Int, State Int] $
      pure . Compose . run . runState 0 . runError

  let all_commutative_tests =
        prepropAllCommutative @BigEffs @BigEffs
          $ pure
          . Compose
          . Compose
          . run
          . runTraceList
          . runOutputList
          . runInputConst 10
          . runState 0

  it "should have the right length" $
    length all_commutative_tests `shouldBe` 3

  traverse_ (prop "Big row is commutative") all_commutative_tests


type TestEffs = '[State Int, Trace, State Int]

type BigEffs = '[State Int, Input Int, Output Bool, Trace]

runTestEffs :: Sem TestEffs a -> IO (Compose ((,) Int) ((,) [String]) a)
runTestEffs =
  pure . Compose . run . runState 0 . runTraceList . subsume

