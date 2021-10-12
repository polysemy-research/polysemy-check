module Polysemy.Check.Arbitrary.Generic where

import Control.Applicative (liftA2)
import Data.Kind (Type)
import GHC.Exts (type (~~))
import Generics.Kind
import Test.QuickCheck
import Polysemy
import Polysemy.Check.Arbitrary.AnyEff
import Polysemy.Internal (send)


------------------------------------------------------------------------------

type a :~~~: b = 'Kon (~~) ':@: a ':@: b


------------------------------------------------------------------------------
-- | Given @'GArbitraryK' a ('RepK' (e m a))@, this typeclass computes
-- generators for every well-typed constructor of @e m a@. It is capable of
-- building generators for GADTs.
class GArbitraryK k (a :: Type) (f :: LoT k -> Type) where
  garbitraryk :: [Gen (f x)]

instance GArbitraryK k a U1 where
  garbitraryk = pure $ pure U1

instance (GArbitraryK1 (f :*: g)) => GArbitraryK Type a (f :*: g) where
  garbitraryk = garbitraryk1

instance (GArbitraryK1 (Field b)) => GArbitraryK Type a (Field b) where
  garbitraryk = garbitraryk1

instance GArbitraryK (k2 -> k) a f => GArbitraryK k a (Exists k2 f) where
  garbitraryk = fmap Exists <$> garbitraryk @(k2 -> k) @a @f

instance (GArbitraryK k a f, GArbitraryK k a g) => GArbitraryK k a (f :+: g) where
  garbitraryk = fmap (fmap L1) (garbitraryk @k @a @f)
             <> fmap (fmap R1) (garbitraryk @k @a @g)

instance GArbitraryK k a (c1 :=>: (c2 :=>: f))
    => GArbitraryK k a ((c1 ':&: c2) :=>: f) where
  garbitraryk =
    fmap
      ((\(SuchThat (SuchThat x)) -> SuchThat x)
            :: (c1 :=>: (c2 :=>: f)) x -> ((c1 ':&: c2) :=>: f) x)
        <$> garbitraryk @k @a

instance {-# OVERLAPPABLE #-} (Interpret c (LoT1 ()), GArbitraryK (Type -> Type) a f)
    => GArbitraryK (Type -> Type) a (c :=>: f) where
  garbitraryk = fmap SuchThat <$> garbitraryk @(Type -> Type) @a @f

instance {-# OVERLAPPING #-} GArbitraryK k a f => GArbitraryK k a ('Kon (a ~~ a) :=>: f) where
  garbitraryk = fmap SuchThat <$> garbitraryk @k @a @f

instance {-# INCOHERENT #-} GArbitraryK k a ('Kon (a ~~ b) :=>: f) where
  garbitraryk = []

instance {-# INCOHERENT #-} GArbitraryK k a ('Kon (b ~~ c) :=>: f) where
  garbitraryk = []

instance (GArbitraryK k a f) => GArbitraryK k a (M1 _1 _2 f) where
  garbitraryk = fmap M1 <$> garbitraryk @k @a


------------------------------------------------------------------------------
-- | @genEff \@e \@a \@m@ gets a generator capable of producing every
-- well-typed GADT constructor of @e m a@.
genEff :: forall e a m. (GArbitraryK Type a (RepK (e m a)), GenericK (e m a)) => Gen (e m a)
genEff = fmap toK $ oneof $ garbitraryk @Type @a @(RepK (e m a))


------------------------------------------------------------------------------
-- | Like @GArbitraryK@, but gets run after we've already discharged the @a
-- ~ T@ GADT constraint.
class GArbitraryK1 (f :: LoT k -> Type) where
  garbitraryk1 :: [Gen (f x)]

instance (GArbitraryK1 f, GArbitraryK1 g) => GArbitraryK1 (f :*: g) where
  garbitraryk1 = liftA2 (liftA2 (:*:)) garbitraryk1 garbitraryk1

instance GArbitraryKTerm t => GArbitraryK1 (Field ('Kon t)) where
  garbitraryk1 = pure $ fmap Field garbitrarykterm

instance GArbitraryK1 f => GArbitraryK1 (M1 _1 _2 f) where
  garbitraryk1 = fmap M1 <$> garbitraryk1

instance GArbitraryK1 U1 where
  garbitraryk1 = pure $ pure U1


class GArbitraryKTerm (t :: Type) where
  garbitrarykterm :: Gen t

instance {-# OVERLAPPING #-} ArbitraryEffOfType a r r => GArbitraryKTerm (Sem r a) where
  garbitrarykterm = do
    SomeEffOfType act <- oneof $ genSomeEffOfType @a @r @r
    pure $ send act

instance {-# OVERLAPPING #-} (CoArbitrary a, GArbitraryKTerm b) => GArbitraryKTerm (a -> b) where
  garbitrarykterm = liftArbitrary garbitrarykterm

instance Arbitrary a => GArbitraryKTerm a where
  garbitrarykterm = arbitrary


