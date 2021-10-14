{-# OPTIONS_GHC -Wno-orphans #-}
module Polysemy.Check.Arbitrary where

import Generics.Kind
import Polysemy
import Polysemy.Check.Arbitrary.AnyEff
import Polysemy.Check.Arbitrary.Generic
import Test.QuickCheck
import Polysemy.Internal (send)


instance (Arbitrary a, ArbitraryEff r r, ArbitraryEffOfType a r r)
      => Arbitrary (Sem r a) where
  arbitrary =
    let terminal = [pure <$> arbitrary]
     in sized $ \n ->
          case n <= 1 of
            True -> oneof terminal
            False -> oneof $
              [ do
                  SomeEffOfType e <- arbitraryActionFromRowOfType @r @r @a
                  pure $ send e
              , do
                  SomeEff e <- arbitraryActionFromRow @r @r
                  k <- liftArbitrary $ scale (`div` 2) arbitrary
                  pure $ send e >>= k
              ] <> terminal


------------------------------------------------------------------------------
-- | Generate any action for effect @e@.
arbitraryAction
    :: forall e r
     . ArbitraryAction (TypesOf e) e r
    => Gen (SomeAction e r)
       -- ^
arbitraryAction = oneof $ genSomeAction @(TypesOf e) @e @r


------------------------------------------------------------------------------
-- | Generate any action for effect @e@ that produces type @a@.
arbitraryActionOfType
    :: forall e a r
     . (GenericK e, GArbitraryK e (RepK e) r a)
    => Gen (e (Sem r) a)
       -- ^
arbitraryActionOfType = genEff @e @r @a


------------------------------------------------------------------------------
-- | Generate any action from any effect in @effs@.
arbitraryActionFromRow
    :: forall (effs :: EffectRow) r
     . ArbitraryEff effs r
    => Gen (SomeEff r)
       -- ^
arbitraryActionFromRow = oneof $ genSomeEff @effs @r


------------------------------------------------------------------------------
-- | Generate any action from any effect in @effs@ that produces type @a@.
arbitraryActionFromRowOfType
    :: forall (effs :: EffectRow) r a
     . ArbitraryEffOfType a effs r
    => Gen (SomeEffOfType r a)
       -- ^
arbitraryActionFromRowOfType = oneof $ genSomeEffOfType @a @effs @r

