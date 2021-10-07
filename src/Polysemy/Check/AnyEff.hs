{-# OPTIONS_GHC -Wredundant-constraints #-}

module Polysemy.Check.AnyEff where

import Data.Kind (Type, Constraint)
import GHC.Exts (type (~~))
import Generics.Kind
import Polysemy
import Polysemy.Internal
import Polysemy.Check.Arbitrary
import Test.QuickCheck


type family TypesOf (f :: LoT Effect -> Type) :: [Type] where
  TypesOf (M1 _1 _2 f) = TypesOf f
  TypesOf (f :+: g) = Append (TypesOf f) (TypesOf g)
  TypesOf (('Kon (~~) ':@: Var1 ':@: 'Kon a) :=>: f) = '[a]
  TypesOf (('Kon ((~~) a) ':@: Var1) :=>: f) = '[a]


------------------------------------------------------------------------------

type family ArbitraryForAll (as :: [Type]) (m :: Type -> Type) :: Constraint where
  ArbitraryForAll '[] f = ()
  ArbitraryForAll (a ': as) f = (Eq a, Show a, GArbitraryK a (RepK (f a)), ArbitraryForAll as f)

type Yo e m = ArbitraryForAll (TypesOf (RepK e)) (e m)

---

data SomeEff e (r :: EffectRow) where
  SomeEff :: (Member e r, Eq a, Show a, Show (e (Sem r) a)) => e (Sem r) a -> SomeEff e r

instance Show (SomeEff e r) where
  show (SomeEff ema) = show ema

instance Show (SomeSomeEff r) where
  show (SomeSomeEff sse) = show sse


data SomeSomeEff (r :: EffectRow) where
  SomeSomeEff :: SomeEff e r -> SomeSomeEff r

class GetAnEffGen (es :: EffectRow) (r :: EffectRow) where
  getAnEffGen :: [Gen (SomeSomeEff r)]

class GetAParticularEffGen (as :: [Type]) (e :: Effect) (r :: EffectRow) where
  getAParticularEffGen :: [Gen (SomeEff e r)]

instance GetAParticularEffGen '[] e r where
  getAParticularEffGen = []

instance
    ( GetAParticularEffGen as e r
    , Eq a
    , Show a
    , Member e r
    , Show (e (Sem r) a)
    , GenericK (e (Sem r) a)
    , GArbitraryK a (RepK (e (Sem r) a))
    )
    => GetAParticularEffGen (a : as) e r
    where
  getAParticularEffGen = (fmap SomeEff $ genEff @e @a @(Sem r)) : getAParticularEffGen @as @e @r

instance GetAnEffGen '[] r where
  getAnEffGen = []

instance
    (GetAnEffGen es r, GetAParticularEffGen (TypesOf (RepK e)) e r)
    => GetAnEffGen (e ': es) r
    where
  getAnEffGen = fmap (fmap SomeSomeEff) (getAParticularEffGen @(TypesOf (RepK e)) @e @r)
             <> getAnEffGen @es @r

