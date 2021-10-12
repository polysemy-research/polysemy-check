module Polysemy.Check.Arbitrary.Generic where

import Data.Kind (Type)
import Generics.Kind
import Test.QuickCheck
import Polysemy


------------------------------------------------------------------------------
-- | Given @'GArbitraryK' a ('RepK' (e m a))@, this typeclass computes
-- generators for every well-typed constructor of @e m a@. It is capable of
-- building generators for GADTs.
class GArbitraryK (e :: Effect) (f :: LoT Effect -> Type) (r :: EffectRow) (a :: Type)  where
  garbitraryk :: [Gen (f (LoT2 (Sem r) a))]

------------------------------------------------------------------------------
-- | @genEff \@e \@a \@m@ gets a generator capable of producing every
-- well-typed GADT constructor of @e m a@.
genEff :: forall e r a. (GenericK e, GArbitraryK e (RepK e) r a) => Gen (e (Sem r) a)

