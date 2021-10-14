{-# LANGUAGE DeriveDataTypeable #-}

module CoverageSpec where

import Polysemy.Check
import Polysemy.State
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Polysemy.Input
import Polysemy.Output
import Polysemy.Error

data Test m a where
  Test1 :: Test m ()
  Test2 :: Int -> Test m ()
  Test3 :: Test m Int
  Test4 :: Test m Bool

deriving instance Show (Test m a)
deriveGenericK ''Test


spec :: Spec
spec = do
  prop "arbitraryAction has a uniform probabilty" $ checkCoverage $ do
    e <- arbitraryAction @Test @'[Test]
    checkUniformProbability 4 e

  prop "arbitraryActionOfType has a uniform probability" $ checkCoverage $ do
    e <- arbitraryActionOfType @Test @()
    checkUniformProbability 2 e

  prop "arbitraryActionFromRow has a uniform probability (small row)" $ checkCoverage $ do
    e <- arbitraryActionFromRow @LittleRow @LittleRow
    checkUniformProbability 6 e

  prop "arbitraryActionFromRow has a uniform probability (large row)" $ checkCoverage $ do
    e <- arbitraryActionFromRow @BigRow @BigRow
    checkUniformProbability 10 e

  prop "arbitraryActionFromRowOfType has a uniform probability (Int)" $ checkCoverage $ do
    e <- arbitraryActionFromRowOfType @BigRow @BigRow @Int
    checkUniformProbability 5 e

  prop "arbitraryActionFromRowOfType has a uniform probability (())" $ checkCoverage $ do
    e <- arbitraryActionFromRowOfType @BigRow @BigRow @()
    checkUniformProbability 6 e


type LittleRow = '[State Int, Test]
type BigRow = '[Error Int, Input Int, Output Int, State Int, Test]


------------------------------------------------------------------------------
-- | @checkUniformProbability n a@ ensures that @a@ gets generated with
-- probability $\frac{1}{n}$.
checkUniformProbability :: (Applicative f, Show a) => Double -> a -> f Property
checkUniformProbability n e = pure $ cover (100 / n) True (constructor e) True


------------------------------------------------------------------------------
-- | Get the constructor name (from a derived Show instance)
constructor :: Show a => a -> String
constructor = unwords . take 1 . words . show

