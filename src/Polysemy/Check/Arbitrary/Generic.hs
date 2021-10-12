module Polysemy.Check.Arbitrary.Generic where

import Control.Applicative (liftA2)
import Data.Kind (Type)
import GHC.Exts (type (~~))
import Generics.Kind hiding (SubstRep)
import Generics.Kind.Unexported
import Polysemy
import Polysemy.Check.Arbitrary.AnyEff
import Polysemy.Internal (send)
import Test.QuickCheck


data family ExistentialFor (e :: Effect)


------------------------------------------------------------------------------
-- | Given @'GArbitraryK' a ('RepK' e) r a@, this typeclass computes
-- generators for every well-typed constructor of @e (Sem r) a@. It is capable
-- of building generators for GADTs.
class GArbitraryK (e :: Effect) (f :: LoT Effect -> Type) (r :: EffectRow) (a :: Type)  where
  garbitraryk :: [Gen (f (LoT2 (Sem r) a))]

instance GArbitraryK e U1 r a where
  garbitraryk = pure $ pure U1

instance (GArbitraryK e f r a, GArbitraryK e g r a) => GArbitraryK e (f :*: g) r a where
  garbitraryk = liftA2 (liftA2 (:*:)) (garbitraryk @e) (garbitraryk @e)

instance GArbitraryKTerm (Interpret f (LoT2 (Sem r) a)) => GArbitraryK e (Field f) r a where
  garbitraryk = pure $ fmap Field $ garbitrarykterm @(Interpret f (LoT2 (Sem r) a))


instance
    ( GArbitraryK e (SubstRep f (ExistentialFor e)) r a
    , SubstRep' f (ExistentialFor e) (LoT2 (Sem r) a)
    ) => GArbitraryK e (Exists Type f) r a where
  garbitraryk = fmap (Exists . unsubstRep @_ @_ @_ @(ExistentialFor e)) <$>
    garbitraryk @e @(SubstRep f (ExistentialFor e)) @r @a

instance (GArbitraryK e f r a, GArbitraryK e g r a) => GArbitraryK e (f :+: g) r a where
  garbitraryk = fmap (fmap L1) (garbitraryk @e @f)
             <> fmap (fmap R1) (garbitraryk @e @g)

instance (Interpret c (LoT2 (Sem r) a), GArbitraryK e f r a) => GArbitraryK e (c :=>: f) r a where
  garbitraryk = fmap (fmap SuchThat) (garbitraryk @e @f)

instance {-# OVERLAPPING #-} GArbitraryK e (c1 :=>: (c2 :=>: f)) r a
    => GArbitraryK e ((c1 ':&: c2) :=>: f) r a where
  garbitraryk =
    fmap
      ((\(SuchThat (SuchThat x)) -> SuchThat x)
            :: (c1 :=>: (c2 :=>: f)) x -> ((c1 ':&: c2) :=>: f) x)
        <$> garbitraryk @e

instance {-# OVERLAPPING #-} GArbitraryK e f r a => GArbitraryK e ('Kon ((~~) a) ':@: Var1 :=>: f) r a where
  garbitraryk = fmap SuchThat <$> garbitraryk @e @f

instance {-# OVERLAPPING #-} GArbitraryK e f r a => GArbitraryK e ('Kon (~~) ':@: Var1 ':@: 'Kon a :=>: f) r a where
  garbitraryk = fmap SuchThat <$> garbitraryk @e @f

instance {-# INCOHERENT #-} GArbitraryK e ('Kon ((~~) b) ':@: Var1 :=>: f) r a where
  garbitraryk = []

instance {-# INCOHERENT #-} GArbitraryK e ('Kon (~~) ':@: Var1 ':@: 'Kon b :=>: f) r a where
  garbitraryk = []

instance (GArbitraryK e f r a) => GArbitraryK e (M1 _1 _2 f) r a where
  garbitraryk = fmap M1 <$> garbitraryk @e


------------------------------------------------------------------------------
-- | @genEff \@e \@a \@m@ gets a generator capable of producing every
-- well-typed GADT constructor of @e m a@.
genEff :: forall e r a. (GenericK e, GArbitraryK e (RepK e) r a) => Gen (e (Sem r) a)
genEff = fmap toK $ oneof $ garbitraryk @e @(RepK e) @r



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

