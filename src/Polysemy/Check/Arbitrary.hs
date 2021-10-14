{-# OPTIONS_GHC -Wno-orphans #-}

module Polysemy.Check.Arbitrary where

import Control.Applicative (liftA2)
import Data.Kind (Type)
import GHC.Exts (type (~~))
import Generics.Kind hiding (SubstRep)
import Generics.Kind.Unexported
import Polysemy
import Polysemy.Internal
import Test.QuickCheck


------------------------------------------------------------------------------
-- | Data family for the instantiation of existential variables. If you want to
-- check properties for an effect @e@ that contains an existential type, the
-- synthesized 'Arbitrary' instance will instantiate all of @e@'s existential
-- types at @'ExistentialFor' e@.
--
-- @'ExistentialFor' e@ must have instances for every dictionary required by
-- @e@, and will likely require an 'Arbitrary' instance.
data family ExistentialFor (e :: Effect)


------------------------------------------------------------------------------
-- | Given @'GArbitraryK' e ('RepK' e) r a@, this typeclass computes
-- generators for every well-typed constructor of @e (Sem r) a@. It is capable
-- of building generators for GADTs.
class GArbitraryK (e :: Effect) (f :: LoT Effect -> Type) (r :: EffectRow) (a :: Type)  where
  garbitraryk :: [Gen (f (LoT2 (Sem r) a))]

instance GArbitraryK e U1 r a where
  garbitraryk = pure $ pure U1

instance (GArbitraryK e f r a, GArbitraryK e g r a) => GArbitraryK e (f :*: g) r a where
  garbitraryk = liftA2 (liftA2 (:*:)) (garbitraryk @e) (garbitraryk @e)

instance Arbitrary (Interpret f (LoT2 (Sem r) a)) => GArbitraryK e (Field f) r a where
  garbitraryk = pure $ fmap Field arbitrary

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
-- | @genEff \@e \@r \@a@ gets a generator capable of producing every
-- well-typed GADT constructor of @e (Sem r) a@.
genEff :: forall e r a. (GenericK e, GArbitraryK e (RepK e) r a) => Gen (e (Sem r) a)
genEff = fmap toK $ oneof $ garbitraryk @e @(RepK e) @r


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


------------------------------------------------------------------------------
-- | Helper function for implementing 'GTypesOf'
type family GTypesOf (f :: LoT Effect -> Type) :: [Type] where
  GTypesOf (M1 _1 _2 f) = GTypesOf f
  GTypesOf (f :+: g) = Append (GTypesOf f) (GTypesOf g)
  GTypesOf (('Kon (~~) ':@: Var1 ':@: 'Kon a) :=>: f) = '[a]
  GTypesOf (('Kon ((~~) a) ':@: Var1) :=>: f) = '[a]
  -- Otherwise, we don't have any constraints on @a@, so we can instantiate it
  -- how we please. Just assume ().
  GTypesOf _1 = '[()]


------------------------------------------------------------------------------
-- | @'TypesOf' e@ is a list of every type that can be bound via @e@'s actions.
--
-- For example, given:
--
-- @
-- data MyEffect m a where
--   Foo :: MyEffect m Int
--   Blah :: Bool -> MyEffect m String
-- @
--
-- the result of @'TypesOf' MyEffect@ is @'[Int, String]@.
type TypesOf (e :: Effect) = GTypesOf (RepK e)


------------------------------------------------------------------------------
-- | @'SomeAction' e r@ is some action for effect @e@ in effect row @r@.
data SomeAction e (r :: EffectRow) where
  SomeAction
      :: (Member e r, Eq a, Show a, CoArbitrary a, Show (e (Sem r) a))
      => e (Sem r) a
         -- ^
      -> SomeAction e r
         -- ^

instance Show (SomeAction e r) where
  show (SomeAction ema) = show ema


------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEff (r :: EffectRow) where
  SomeEff
      :: (Member e r, Eq a, Show a, CoArbitrary a, Show (e (Sem r) a))
      => e (Sem r) a
         -- ^
      -> SomeEff r
         -- ^

instance Show (SomeEff r) where
  show (SomeEff sse) = show sse


------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEffOfType (r :: EffectRow) a where
  SomeEffOfType
      :: (Member e r, Eq a, Show a, CoArbitrary a, Show (e (Sem r) a))
      => e (Sem r) a
         -- ^
      -> SomeEffOfType r a
         -- ^

instance Show (SomeEffOfType r a) where
  show (SomeEffOfType sse) = show sse


------------------------------------------------------------------------------
-- | @'ArbitraryEff' es r@ lets you randomly generate an action in any of
-- the effects @es@.
class ArbitraryEff (es :: EffectRow) (r :: EffectRow) where
  genSomeEff :: [Gen (SomeEff r)]

instance ArbitraryEff '[] r where
  genSomeEff = []

instance
    (ArbitraryEff es r, ArbitraryAction (TypesOf e) e r)
    => ArbitraryEff (e ': es) r
    where
  genSomeEff = fmap (fmap (\(SomeAction e) -> SomeEff e)) (genSomeAction @(TypesOf e) @e @r)
             <> genSomeEff @es @r


------------------------------------------------------------------------------
-- | @'ArbitraryEffOfType' a es r@ lets you randomly generate an action in any of
-- the effects @es@ that produces type @a@.
class ArbitraryEffOfType (a :: Type) (es :: EffectRow) (r :: EffectRow) where
  genSomeEffOfType :: [Gen (SomeEffOfType r a)]

instance ArbitraryEffOfType a '[] r where
  genSomeEffOfType = []

instance
    ( Eq a
    , Show a
    , Show (e (Sem r) a)
    , ArbitraryEffOfType a es r
    , GenericK e
    , GArbitraryK e (RepK e) r a
    , CoArbitrary a
    , Member e r
    )
    => ArbitraryEffOfType a (e ': es) r
    where
  genSomeEffOfType
    = (fmap (SomeEffOfType @e @r . toK) <$> garbitraryk @e @(RepK e) @r)
    <> genSomeEffOfType @a @es @r


------------------------------------------------------------------------------
-- | @'ArbitraryAction' as e r@ lets you randomly generate an action
-- producing any type in @as@ from the effect @e@.
class ArbitraryAction (as :: [Type]) (e :: Effect) (r :: EffectRow) where
  genSomeAction :: [Gen (SomeAction e r)]

instance ArbitraryAction '[] e r where
  genSomeAction = []

instance
    ( ArbitraryAction as e r
    , Eq a
    , Show a
    , Member e r
    , Show (e (Sem r) a)
    , GenericK e
    , CoArbitrary a
    , GArbitraryK e (RepK e) r a
    )
    => ArbitraryAction (a : as) e r
    where
  genSomeAction = (fmap SomeAction $ genEff @e @r @a) : genSomeAction @as @e @r

