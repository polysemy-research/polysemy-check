module Polysemy.Check.Arbitrary where

import Control.Applicative (liftA2)
import Data.Kind (Type)
import GHC.Exts (type (~~))
import Generics.Kind
import Test.QuickCheck


------------------------------------------------------------------------------

type a :~~~: b = 'Kon (~~) ':@: a ':@: b


------------------------------------------------------------------------------
-- | Given @'GArbitraryK' a ('RepK' (e m a))@, this typeclass computes
-- generators for every well-typed constructor of @e m a@. It is capable of
-- building generators for GADTs.
class GArbitraryK (a :: Type) (f :: LoT Type -> Type) where
  garbitraryk :: [Gen (f x)]

instance GArbitraryK a U1 where
  garbitraryk = pure $ pure U1

instance (GArbitraryK a f, GArbitraryK a g) => GArbitraryK a (f :*: g) where
  garbitraryk = liftA2 (liftA2 (:*:)) (garbitraryk @a) (garbitraryk @a)

instance (GArbitraryK a f, GArbitraryK a g) => GArbitraryK a (f :+: g) where
  garbitraryk = fmap (fmap L1) (garbitraryk @a @f)
             <> fmap (fmap R1) (garbitraryk @a @g)

instance GArbitraryK1 f => GArbitraryK a ('Kon (a ~~ a) :=>: f) where
  garbitraryk = fmap SuchThat <$> garbitraryk1

instance {-# INCOHERENT #-} GArbitraryK a ('Kon (a ~~ b) :=>: f) where
  garbitraryk = []

instance {-# INCOHERENT #-} GArbitraryK a ('Kon (b ~~ c) :=>: f) where
  garbitraryk = []

instance (GArbitraryK a f) => GArbitraryK a (M1 _1 _2 f) where
  garbitraryk = fmap M1 <$> garbitraryk @a


------------------------------------------------------------------------------
-- | @genEff \@e \@a \@m@ gets a generator capable of producing every
-- well-typed GADT constructor of @e m a@.
genEff :: forall e a m. (GArbitraryK a (RepK (e m a)), GenericK (e m a)) => Gen (e m a)
genEff = fmap toK $ oneof $ garbitraryk @a @(RepK (e m a))


------------------------------------------------------------------------------
-- | Like @GArbitraryK@, but gets run after we've already discharged the @a
-- ~ T@ GADT constraint.
class GArbitraryK1 (f :: LoT Type -> Type) where
  garbitraryk1 :: [Gen (f x)]

instance (GArbitraryK1 f, GArbitraryK1 g) => GArbitraryK1 (f :*: g) where
  garbitraryk1 = liftA2 (liftA2 (:*:)) garbitraryk1 garbitraryk1

instance Arbitrary t => GArbitraryK1 (Field ('Kon t)) where
  garbitraryk1 = pure $ fmap Field arbitrary

instance (GArbitraryK1 f) => GArbitraryK1 (M1 _1 _2 f) where
  garbitraryk1 = fmap M1 <$> garbitraryk1

instance GArbitraryK1 U1 where
  garbitraryk1 = pure $ pure U1

