{-# LANGUAGE QuantifiedConstraints   #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Generics.Kind.Unexported where

import Generics.Kind hiding (SubstRep)


class SubstRep' (f :: LoT (t -> k) -> *) (x :: t) (xs :: LoT k) where
  type family SubstRep f x :: LoT k -> *
  substRep   :: f (x ':&&: xs) -> SubstRep f x xs
  unsubstRep :: SubstRep f x xs -> f (x ':&&: xs)

instance SubstRep' U1 x xs where
  type SubstRep U1 x = U1
  substRep   U1 = U1
  unsubstRep U1 = U1

instance (SubstRep' f x xs, SubstRep' g x xs) => SubstRep' (f :+: g) x xs where
  type SubstRep (f :+: g)  x = (SubstRep f x) :+: (SubstRep g x)
  substRep   (L1 x) = L1 (substRep   x)
  substRep   (R1 x) = R1 (substRep   x)
  unsubstRep (L1 x) = L1 (unsubstRep x)
  unsubstRep (R1 x) = R1 (unsubstRep x)

instance (SubstRep' f x xs, SubstRep' g x xs) => SubstRep' (f :*: g) x xs where
  type SubstRep (f :*: g) x = (SubstRep f x) :*: (SubstRep g x)
  substRep   (x :*: y) = substRep   x :*: substRep   y
  unsubstRep (x :*: y) = unsubstRep x :*: unsubstRep y

instance SubstRep' f x xs => SubstRep' (M1 i c f) x xs where
  type SubstRep (M1 i c f) x = M1 i c (SubstRep f x)
  substRep   (M1 x) = M1 (substRep   x)
  unsubstRep (M1 x) = M1 (unsubstRep x)

-- The context says that @Interpret (SubstAtom c x) xs@
-- and @Interpret c (x ':&&: xs)@ are equivalent.
-- But because @Interpret@ is a type family, and the right-hand side of
-- a quantified constraint must be a class, we must use "class synonyms"
-- @InterpretCons@ and @InterpretSubst@.
instance ( Interpret (SubstAtom c x) xs => InterpretCons c x xs
         , Interpret c (x ':&&: xs) => InterpretSubst c x xs
         , SubstRep' f x xs )
         => SubstRep' (c :=>: f) x xs where
  type SubstRep (c :=>: f) x = (SubstAtom c x) :=>: (SubstRep f x)
  substRep   (SuchThat x) = with @(InterpretSubst c x xs) $ SuchThat (substRep   x)
  unsubstRep (SuchThat x) = with @(InterpretCons  c x xs) $ SuchThat (unsubstRep x)

with :: forall c t. (c => t) -> (c => t)
with x = x

class    Interpret c (x ':&&: xs) => InterpretCons c x xs
instance Interpret c (x ':&&: xs) => InterpretCons c x xs

class    Interpret (SubstAtom c x) xs => InterpretSubst c x xs
instance Interpret (SubstAtom c x) xs => InterpretSubst c x xs

instance (Interpret (SubstAtom t x) xs ~ Interpret t (x ':&&: xs))
         => SubstRep' (Field t) x xs where
  type SubstRep (Field t) x = Field (SubstAtom t x)
  substRep   (Field x) = Field x
  unsubstRep (Field x) = Field x

type family SubstAtom (f :: Atom (t -> k) d) (x :: t) :: Atom k d where
  SubstAtom ('Var 'VZ)     x = 'Kon x
  SubstAtom ('Var ('VS v)) x = 'Var v
  SubstAtom ('Kon t)       x = 'Kon t
  SubstAtom (t1 ':@: t2)   x = (SubstAtom t1 x) ':@: (SubstAtom t2 x)
  SubstAtom (t1 ':&: t2)   x = (SubstAtom t1 x) ':&: (SubstAtom t2 x)

