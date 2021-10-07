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
type family TypesOf (f :: LoT Effect -> Type) :: [Type] where
  TypesOf (M1 _1 _2 f) = TypesOf f
  TypesOf (f :+: g) = Append (TypesOf f) (TypesOf g)
  TypesOf (('Kon (~~) ':@: Var1 ':@: 'Kon a) :=>: f) = '[a]
  TypesOf (('Kon ((~~) a) ':@: Var1) :=>: f) = '[a]


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


------------------------------------------------------------------------------
-- | @'SomeEff' r@ is some action for some effect in the effect row @r@.
data SomeEff (r :: EffectRow) where
  SomeEff :: SomeAction e r -> SomeEff r


------------------------------------------------------------------------------
-- | @'GenerateSomeEff' es r@ lets you randomly generate an action in any of
-- the effects @es@.
class GenerateSomeEff (es :: EffectRow) (r :: EffectRow) where
  genSomeEff :: [Gen (SomeEff r)]

instance GenerateSomeEff '[] r where
  genSomeEff = []

instance
    (GenerateSomeEff es r, GenerateSomeAction (TypesOf (RepK e)) e r)
    => GenerateSomeEff (e ': es) r
    where
  genSomeEff = fmap (fmap SomeEff) (genSomeAction @(TypesOf (RepK e)) @e @r)
             <> genSomeEff @es @r


------------------------------------------------------------------------------
-- | @'GenerateSomeAction' as e r@ lets you randomly generate an action
-- producing any type in @as@ from the effect @e@.
class GenerateSomeAction (as :: [Type]) (e :: Effect) (r :: EffectRow) where
  genSomeAction :: [Gen (SomeAction e r)]

instance GenerateSomeAction '[] e r where
  genSomeAction = []

instance
    ( GenerateSomeAction as e r
    , Eq a
    , Show a
    , Member e r
    , Show (e (Sem r) a)
    , GenericK (e (Sem r) a)
    , GArbitraryK a (RepK (e (Sem r) a))
    )
    => GenerateSomeAction (a : as) e r
    where
  genSomeAction = (fmap SomeAction $ genEff @e @a @(Sem r)) : genSomeAction @as @e @r

