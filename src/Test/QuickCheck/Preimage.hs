{-# OPTIONS_GHC -Wno-orphans #-}
module Test.QuickCheck.Preimage where

import Test.QuickCheck
import Polysemy
import Polysemy.Check.Arbitrary
import Data.Foldable
import Control.Monad (void)
import Polysemy.Internal (send)
import Polysemy.Internal.Union.Inject


instance ArbitraryEffOfType a r r => Arbitrary (SomeEffOfType r a) where
  arbitrary = arbitraryActionFromRowOfType @r @r @a

instance ArbitraryEff r r => Arbitrary (SomeEff r) where
  arbitrary = arbitraryActionFromRow @r @r

-- instance (Arbitrary a, ArbitraryEff r r, ArbitraryEffOfType a r r)
--       => ArbitraryPreimage (Sem r a) where
--   type Preimage (Sem r a) = ([SomeEff r], SomeEffOfType r a)
--   fromPreimage (effs, SomeEffOfType m) = do
--     for_ effs $ ((\case
--       SomeEff (e :: e m x) -> void $ (send e :: Sem r x)) :: SomeEff r -> Sem r ())
--     send m


forallPreimage
    :: (ArbitraryPreimage a, Arbitrary (Preimage a), Show (Preimage a), Testable prop)
    => (a -> prop) -> Property
forallPreimage f = forAllShrinkShow arbitrary shrink show $ f . fromPreimage


liftGen
    :: forall effs a
     . Arbitrary (Sem effs a)
    => Gen (SomeSem effs a)
liftGen = do
  a <- arbitrary @(Sem effs a)
  pure $ SomeSem $ inject a



