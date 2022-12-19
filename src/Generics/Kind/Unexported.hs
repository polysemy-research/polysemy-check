module Generics.Kind.Unexported where

import Generics.Kind hiding (SubstRep, SubstRep')


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

instance (Interpret (SubstAtom c x) xs, Interpret c (x ':&&: xs), SubstRep' f x xs)
         => SubstRep' (c :=>: f) x xs where
  type SubstRep (c :=>: f) x = (SubstAtom c x) :=>: (SubstRep f x)
  substRep   (SuchThat x) = SuchThat (substRep   x)
  unsubstRep (SuchThat x) = SuchThat (unsubstRep x)

instance (Interpret (SubstAtom t x) xs ~ Interpret t (x ':&&: xs))
         => SubstRep' (Field t) x xs where
  type SubstRep (Field t) x = Field (SubstAtom t x)
  substRep   (Field x) = Field x
  unsubstRep (Field x) = Field x

