module Polysemy.Check.Arbitrary.Generic where

import Data.Kind (Type)
import Generics.Kind
import Test.QuickCheck


------------------------------------------------------------------------------
-- | Given @'GArbitraryK' a ('RepK' (e m a))@, this typeclass computes
-- generators for every well-typed constructor of @e m a@. It is capable of
-- building generators for GADTs.
class GArbitraryK k (a :: Type) (f :: LoT k -> Type) where
  garbitraryk :: [Gen (f x)]

------------------------------------------------------------------------------
-- | @genEff \@e \@a \@m@ gets a generator capable of producing every
-- well-typed GADT constructor of @e m a@.
genEff :: forall e a m. (GArbitraryK Type a (RepK (e m a)), GenericK (e m a)) => Gen (e m a)

