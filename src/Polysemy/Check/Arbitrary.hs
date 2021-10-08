module Polysemy.Check.Arbitrary where

import Generics.Kind
import Polysemy
import Polysemy.Check.Arbitrary.AnyEff
import Polysemy.Check.Arbitrary.Generic
import Test.QuickCheck


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
     . (GenericK (e (Sem r) a), GArbitraryK a (RepK (e (Sem r) a)))
    => Gen (e (Sem r) a)
       -- ^
arbitraryActionOfType = genEff @e @a @(Sem r)


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

