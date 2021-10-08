{-# OPTIONS_GHC -Wredundant-constraints #-}

module Polysemy.Check.AnyEff where

import Data.Kind (Type, Constraint)
import GHC.Exts (type (~~))
import Generics.Kind
import Polysemy
import Polysemy.Internal
import Polysemy.Check.Arbitrary
import Test.QuickCheck


------------------------------------------------------------------------------
-- | @'TypesOf' ('RepK' e)@ is a list of every type that can be bound via @e@'s
-- effects.
--
-- For example, given:
--
-- @
-- data MyEffect m a where
--   Foo :: MyEffect m Int
--   Blah :: Bool -> MyEffect m String
-- @
--
-- the result of @'TypesOf' ('RepK' MyEffect)@ is @'[Int, String]@.
type family GTypesOf (f :: LoT Effect -> Type) :: [Type] where
  GTypesOf (M1 _1 _2 f) = GTypesOf f
  GTypesOf (f :+: g) = Append (GTypesOf f) (GTypesOf g)
  GTypesOf (('Kon (~~) ':@: Var1 ':@: 'Kon a) :=>: f) = '[a]
  GTypesOf (('Kon ((~~) a) ':@: Var1) :=>: f) = '[a]

type TypesOf (e :: Effect) = GTypesOf (RepK e)


------------------------------------------------------------------------------
-- | A type family that expands to a 'GArbitraryK' constaint for every type in
-- the first list.
type family ArbitraryForAll (as :: [Type]) (m :: Type -> Type) :: Constraint where
  ArbitraryForAll '[] f = ()
  ArbitraryForAll (a ': as) f = (Eq a, Show a, GArbitraryK a (RepK (f a)), ArbitraryForAll as f)


------------------------------------------------------------------------------
-- | @'SomeAction' e r@ is some action for effect @e@ in effect row @r@.
data SomeAction e (r :: EffectRow) where
  SomeAction :: (Member e r, Eq a, Show a, Show (e (Sem r) a)) => e (Sem r) a -> SomeAction e r

instance Show (SomeAction e r) where
  show (SomeAction ema) = show ema

instance Show (SomeEff r) where
  show (SomeEff sse) = show sse


arbitraryAction
    :: forall e r
     . ArbitraryAction (TypesOf e) e r
    => Gen (SomeAction e r)
arbitraryAction = oneof $ genSomeAction @(TypesOf e) @e @r


arbitraryActionOfType
    :: forall e a r
     . (GenericK (e (Sem r) a), GArbitraryK a (RepK (e (Sem r) a)))
    => Gen (e (Sem r) a)
arbitraryActionOfType = genEff @e @a @(Sem r)


arbitraryActionFromRow
    :: forall (effs :: EffectRow) r
     . ArbitraryEff effs r
    => Gen (SomeEff r)
arbitraryActionFromRow = oneof $ genSomeEff @effs @r


arbitraryActionFromRowOfType
    :: forall (effs :: EffectRow) r a
     . ArbitraryEffOfType a effs r
    => Gen (SomeEffOfType r a)
arbitraryActionFromRowOfType = oneof $ genSomeEffOfType @a @effs @r


------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEff (r :: EffectRow) where
  SomeEff :: (Member e r, Eq a, Show a, Show (e (Sem r) a)) => e (Sem r) a -> SomeEff r

------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEffOfType (r :: EffectRow) a where
  SomeEffOfType :: (Member e r, Eq a, Show a, Show (e (Sem r) a)) => e (Sem r) a -> SomeEffOfType r a


------------------------------------------------------------------------------
-- | @'GenerateSomeEff' es r@ lets you randomly generate an action in any of
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
-- | @'GenerateSomeEff' es r@ lets you randomly generate an action in any of
-- the effects @es@.
class ArbitraryEffOfType (a :: Type) (es :: EffectRow) (r :: EffectRow) where
  genSomeEffOfType :: [Gen (SomeEffOfType r a)]

instance ArbitraryEffOfType a '[] r where
  genSomeEffOfType = []

instance
    ( Eq a
    , Show a
    , Show (e (Sem r) a)
    , ArbitraryEffOfType a es r
    , GenericK (e (Sem r) a)
    , GArbitraryK a (RepK (e (Sem r) a))
    , Member e r
    )
    => ArbitraryEffOfType a (e ': es) r
    where
  genSomeEffOfType
    = fmap SomeEffOfType (arbitraryActionOfType @e @a @r)
    : genSomeEffOfType @a @es @r



------------------------------------------------------------------------------
-- | @'GenerateSomeAction' as e r@ lets you randomly generate an action
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
    , GenericK (e (Sem r) a)
    , GArbitraryK a (RepK (e (Sem r) a))
    )
    => ArbitraryAction (a : as) e r
    where
  genSomeAction = (fmap SomeAction $ genEff @e @a @(Sem r)) : genSomeAction @as @e @r

