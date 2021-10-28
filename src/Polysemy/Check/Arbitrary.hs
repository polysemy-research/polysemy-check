-- {-# LANGUAGE NoAllowAmbiguousTypes        #-}
{-# LANGUAGE QuantifiedConstraints   #-}
{-# LANGUAGE TupleSections           #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ViewPatterns #-}
module Polysemy.Check.Arbitrary where

import Control.Applicative (liftA2)
import Control.Monad (void)
import Data.Foldable (for_)
import Data.Kind (Type)
import GHC.Exts (type (~~))
import Generics.Kind hiding (SubstRep)
import Generics.Kind.Unexported
import Polysemy
import Polysemy.Internal
import Test.QuickCheck
import GHC.Generics


------------------------------------------------------------------------------
-- | Data family for the instantiation of existential variables. If you want to
-- check properties for an effect @e@ that contains an existential type, the
-- synthesized 'Arbitrary' instance will instantiate all of @e@'s existential
-- types at @'ExistentialFor' e@.
--
-- @'ExistentialFor' e@ must have instances for every dictionary required by
-- @e@, and will likely require an 'Arbitrary' instance.
data family ExistentialFor (e :: Effect)


class Checkable (e :: Effect) where
  hoistEff :: e (Shrinkable r) a -> e (Sem r) a
  default hoistEff
      :: (GHoist (RepK e) (Shrinkable r) (Sem r) a, GenericK e)
      => e (Shrinkable r) a
      -> e (Sem r) a
  hoistEff = toK . ghoist (fromPreimage . getCompose) . fromK

  shrinkEff :: ArbitraryEffOfType a r r => ArbitraryEff r r => e (Shrinkable r) a -> [e (Shrinkable r) a]
  default shrinkEff
      :: ArbitraryEff r r
      => ArbitraryEffOfType a r r
      => (GenericK e, GShrink (RepK e) r a)
      => e (Shrinkable r) a
      -> [e (Shrinkable r) a]
  shrinkEff = fmap toK . gshrink . fromK


newtype Compose f g a = Compose { getCompose :: f (g a) }
  deriving (Show, Eq, Generic)

instance Arbitrary (f (g a)) => Arbitrary (Compose f g a) where
  arbitrary = fmap Compose arbitrary
  shrink = genericShrink

instance (ArbitraryEff r r, ArbitraryEffOfType a r r) => Arbitrary (SomeEffOfType r a) where
  arbitrary = arbitraryActionFromRowOfType @r @r @a
  shrink (SomeEffOfType ectltlp_l_srsra) = SomeEffOfType <$> shrinkEff ectltlp_l_srsra

instance (ArbitraryEff r r) => Arbitrary (SomeEff r) where
  arbitrary = arbitraryActionFromRow @r @r
  shrink (SomeEff ectltlp_l_srsra) = SomeEff <$> shrinkEff ectltlp_l_srsra

instance (ArbitraryAction (TypesOf e) e r) => Arbitrary (SomeAction e r) where
  arbitrary = arbitraryAction @e @r
  shrink (SomeAction ectltlp_l_srsra) = SomeAction <$> shrinkEff ectltlp_l_srsra

instance (GenericK e, GArbitraryK e (RepK e) r a, Checkable e, ArbitraryEff r r, ArbitraryEffOfType a r r)
      => Arbitrary ((e :: Effect) (Shrinkable r) a) where
  arbitrary = arbitraryActionOfType @e @a @r
  shrink = shrinkEff

class ArbitraryPreimage a where
  type Preimage a
  fromPreimage :: Preimage a -> a

forAllPreimage
    :: (Arbitrary (Preimage a), Show (Preimage a), ArbitraryPreimage a, Testable prop)
    => (a -> prop)
    -> Property
forAllPreimage prop = forAllP $ prop . fromPreimage

forAllP
    :: (Arbitrary a, Show a, Testable prop)
    => (a -> prop)
    -> Property
forAllP prop = forAllShrinkShow arbitrary shrink show $ prop

forAllP'
    :: (Arbitrary a, Show a, Testable prop)
    => Gen a
    -> (a -> prop)
    -> Property
forAllP' gen prop = forAllShrinkShow gen shrink show $ prop

instance ArbitraryPreimage (Sem r a) where
  type Preimage (Sem r a) = ([SomeEff r], SomeEffOfType r a)
  fromPreimage (effs, SomeEffOfType m) = do
    for_ effs sendSomeEff
    send $ hoistEff m

instance Checkable e
      => ArbitraryPreimage ((e :: Effect) (Sem r) a) where
  type Preimage (e (Sem r) a) = e (Shrinkable r) a
  fromPreimage = hoistEff


sendSomeEff :: SomeEff r -> Sem r ()
sendSomeEff (SomeEff e) = void $ send $ hoistEff e

type Shrinkable r = Compose ((,) [SomeEff r]) (SomeEffOfType r)

class GHoist (f :: LoT Effect -> Type) m n a where
  ghoist :: Functor n => (forall x. m x -> n x) -> f (LoT2 m a) -> f (LoT2 n a)

instance GHoist f m n a => GHoist (M1 _1 _2 f) m n a where
  ghoist nt = M1 . ghoist nt . unM1

instance (GHoist f m n a, GHoist g m n a) => GHoist (f :+: g) m n a where
  ghoist nt (L1 f) = L1 $ ghoist nt f
  ghoist nt (R1 g) = R1 $ ghoist nt g

instance (GHoist f m n a, GHoist g m n a) => GHoist (f :*: g) m n a where
  ghoist nt (f :*: g) = ghoist nt f :*: ghoist nt g

instance (Interpret x (LoT2 m a) ~ Interpret x (LoT2 n a)) => GHoist (Field (Var0 ':@: x)) m n a where
  ghoist nt (Field x) = Field $ nt x

instance GHoist (Field ('Kon c)) m n a where
  ghoist _ (Field x) = Field x

instance GHoist (Field f) m n a =>
         GHoist (Field ('Kon ((->) c) ':@: f)) m n a where
  ghoist nt (Field x) = Field $ unField . ghoist @(Field f) nt . Field @f @(LoT2 m a) . x

instance ( Interpret c (LoT2 m a) => InterpretSuchThat c n a
         , GHoist f m n a
         ) => GHoist (c :=>: f) m n a where
  ghoist nt (SuchThat x) = with @(InterpretSuchThat c n a) $ SuchThat (ghoist nt x)

class    Interpret c (LoT2 n a) => InterpretSuchThat c n a
instance Interpret c (LoT2 n a) => InterpretSuchThat c n a


class GShrink (f :: LoT Effect -> Type) r a where
  gshrink :: f (LoT2 (Shrinkable r) a) -> [f (LoT2 (Shrinkable r) a)]

instance GShrink f r a => GShrink (M1 _1 _2 f) r a where
  gshrink (M1 f) = M1 <$> gshrink f

instance (GShrink f r a, GShrink g r a) => GShrink (f :*: g) r a where
  gshrink (f :*: g) = fmap (f :*:) (gshrink g) <> fmap (:*: g) (gshrink f)

instance (GShrink f r a, GShrink g r a) => GShrink (f :+: g) r a where
  gshrink (L1 f) = L1 <$> gshrink f
  gshrink (R1 g) = R1 <$> gshrink g

instance GShrink U1 r a where
  gshrink U1 = []

instance GShrink V1 r a where
  gshrink _ = []

instance Arbitrary (Interpret c (LoT2 (Shrinkable r) a)) => GShrink (Field c) r a where
  gshrink (Field c) = Field <$> shrink c

instance GShrink f r a => GShrink (c :=>: f) r a where
  gshrink (SuchThat f) = SuchThat <$> gshrink f

instance GShrink (Exists Type f) r a where
  gshrink (Exists _) = []




-- instance (GHoist f m n a) => GHoist ('Kon ((~~) b) ':@: Var1 :=>: f) m n a where
--   ghoist nt (SuchThat x) = SuchThat $ ghoist nt x

-- instance (GHoist f m n a) => GHoist ('Kon (~~) ':@: Var1 ':@: 'Kon x :=>: f) m n a where
--   ghoist nt (SuchThat x) = SuchThat $ ghoist nt x

class (SubstRep' f t (LoT2 m a), SubstRep' f t (LoT2 n a), GHoist (SubstRep f t) m n a) => GHoist_SubstRep f t m n a
instance (SubstRep' f t (LoT2 m a), SubstRep' f t (LoT2 n a), GHoist (SubstRep f t) m n a) => GHoist_SubstRep f t m n a

instance (forall x. GHoist_SubstRep f x m n a) => GHoist (Exists Type f) m n a where
  ghoist nt (Exists (x :: f (t ':&&: z))) =
    with @(GHoist_SubstRep f t m n a) $
      Exists $ unsubstRep @_ @_ @_ @t $ ghoist @(SubstRep f t) nt $ substRep @_ @_ @_ @t x

instance GHoist U1 m n a where
  ghoist _ U1 = U1




------------------------------------------------------------------------------
-- | Given @'GArbitraryK' e ('RepK' e) r a@, this typeclass computes
-- generators for every well-typed constructor of @e (Shrinkable r) a@. It is capable
-- of building generators for GADTs.
class GArbitraryK (e :: Effect) (f :: LoT Effect -> Type) (r :: EffectRow) (a :: Type)  where
  garbitraryk :: [Gen (f (LoT2 (Shrinkable r) a))]

instance GArbitraryK e U1 r a where
  garbitraryk = pure $ pure U1

instance (GArbitraryK e f r a, GArbitraryK e g r a) => GArbitraryK e (f :*: g) r a where
  garbitraryk = liftA2 (liftA2 (:*:)) (garbitraryk @e) (garbitraryk @e)

instance Arbitrary (Interpret f (LoT2 (Shrinkable r) a)) => GArbitraryK e (Field f) r a where
  garbitraryk = pure $ fmap Field arbitrary

instance
    ( GArbitraryK e (SubstRep f (ExistentialFor e)) r a
    , SubstRep' f (ExistentialFor e) (LoT2 (Shrinkable r) a)
    ) => GArbitraryK e (Exists Type f) r a where
  garbitraryk = fmap (Exists . unsubstRep @_ @_ @_ @(ExistentialFor e)) <$>
    garbitraryk @e @(SubstRep f (ExistentialFor e)) @r @a

instance (GArbitraryK e f r a, GArbitraryK e g r a) => GArbitraryK e (f :+: g) r a where
  garbitraryk = fmap (fmap L1) (garbitraryk @e @f)
             <> fmap (fmap R1) (garbitraryk @e @g)

instance (Interpret c (LoT2 (Shrinkable r) a), GArbitraryK e f r a) => GArbitraryK e (c :=>: f) r a where
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
            False -> frequency $
              [ (2,) $ do
                  SomeEffOfType e <- arbitraryActionFromRowOfType @r @r @a
                  pure $ send $ hoistEff e
              , (8,) $ do
                  SomeEff e <- arbitraryActionFromRow @r @r
                  k <- liftArbitrary $ scale (`div` 2) arbitrary
                  pure $ send (hoistEff e) >>= k
              ] <> fmap (1,) terminal

------------------------------------------------------------------------------
-- | @genEff \@e \@r \@a@ gets a generator capable of producing every
-- well-typed GADT constructor of @e (Shrinkable r) a@.
genEff :: forall e r a. (GenericK e, GArbitraryK e (RepK e) r a) => Gen (e (Shrinkable r) a)
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
    => Gen (e (Shrinkable r) a)
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
      :: ( Member e r
         , Eq a
         , Show a
         , CoArbitrary a
         , Show (e (Shrinkable r) a)
         , Checkable e
         , ArbitraryEffOfType a r r
         , ArbitraryEff r r
         )
      => e (Shrinkable r) a
         -- ^
      -> SomeAction e r
         -- ^

instance Show (SomeAction e r) where
  show (SomeAction ema) = show ema


------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEff (r :: EffectRow) where
  SomeEff
      :: ( Member e r
         , Eq a
         , Show a
         , CoArbitrary a
         , Show (e (Shrinkable r) a)
         , Checkable e
         , ArbitraryEffOfType a r r
         , ArbitraryEff r r
         )
      => e (Shrinkable r) a
         -- ^
      -> SomeEff r
         -- ^

instance Show (SomeEff r) where
  show (SomeEff sse) = show sse


------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEffOfType (r :: EffectRow) a where
  SomeEffOfType
      :: ( Member e r
         , Eq a
         , Show a
         , CoArbitrary a
         , Show (e (Shrinkable r) a)
         , Checkable e
         , ArbitraryEffOfType a r r
         , ArbitraryEff r r
         )
      => e (Shrinkable r) a
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
    , Show (e (Shrinkable r) a)
    , ArbitraryEffOfType a es r
    , GenericK e
    , GArbitraryK e (RepK e) r a
    , CoArbitrary a
    , Member e r
    , Checkable e
    , ArbitraryEffOfType a r r
    , ArbitraryEff r r
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
    , Show (e (Shrinkable r) a)
    , GenericK e
    , CoArbitrary a
    , GArbitraryK e (RepK e) r a
    , Checkable e
         , ArbitraryEffOfType a r r
         , ArbitraryEff r r
    )
    => ArbitraryAction (a : as) e r
    where
  genSomeAction = (fmap SomeAction $ genEff @e @r @a) : genSomeAction @as @e @r

