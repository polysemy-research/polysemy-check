{-# OPTIONS_GHC -Wredundant-constraints #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Lib where

import           Control.Applicative (liftA2)
import           Data.Foldable (traverse_)
import           Data.Kind (Type, Constraint)
import           Data.Set (Set)
import qualified Data.Set as S
import           GHC.Exts (type (~~))
import           Generics.Kind
import           Generics.Kind.TH
import           Polysemy
import           Polysemy.Internal
import           Polysemy.Internal.Union
import           Polysemy.Law
import           Polysemy.Output
import           Polysemy.State
import           Type.Reflection


data ATypeRep where
  ATypeRep :: TypeRep (a :: Type) -> ATypeRep

instance Eq ATypeRep where
  ATypeRep a == ATypeRep b = (==) (SomeTypeRep a) (SomeTypeRep b)

instance Ord ATypeRep where
  ATypeRep a `compare` ATypeRep b = compare (SomeTypeRep a) (SomeTypeRep b)

type family TypesOf (f :: LoT Effect -> Type) :: [Type] where
  TypesOf (M1 _1 _2 f) = TypesOf f
  TypesOf (f :+: g) = Append (TypesOf f) (TypesOf g)
  TypesOf (('Kon (~~) ':@: Var1 ':@: 'Kon a) :=>: f) = '[a]
  TypesOf (('Kon ((~~) a) ':@: Var1) :=>: f) = '[a]

data CircleBuffer m a where
  PutE :: Int -> CircleBuffer m ()
  GetE :: CircleBuffer m Int
  LenE :: CircleBuffer m Int

deriving instance Show (CircleBuffer m a)

data Worker m a where
  Worker :: Bool -> Int -> Worker m ()

deriving instance Show (Worker m ())

makeSem ''CircleBuffer
deriveGenericK ''CircleBuffer
deriveGenericK ''Worker

deriveGenericK ''State
deriveGenericK ''Output

deriving instance Show s => Show (State s (Sem r) a)
deriving instance Show o => Show (Output o (Sem r) a)

type a :~~~: b = 'Kon (~~) ':@: a ':@: b

------------------------------------------------------------------------------

class GTypesOf (f :: LoT Effect -> Type) where
  gtypesofk :: Set ATypeRep

instance (GTypesOf f, GTypesOf g) => GTypesOf (f :+: g) where
  gtypesofk = gtypesofk @f <> gtypesofk @g

instance Typeable a => GTypesOf (Var1 :~~~: 'Kon (a :: Type) :=>: _1) where
  gtypesofk = S.singleton $ ATypeRep $ typeRep @a

instance (GTypesOf f) => GTypesOf (M1 _1 _2 f) where
  gtypesofk = gtypesofk @f


------------------------------------------------------------------------------

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

type family ArbitraryForAll (as :: [Type]) (m :: Type -> Type) :: Constraint where
  ArbitraryForAll '[] f = ()
  ArbitraryForAll (a ': as) f = (Eq a, Show a, GArbitraryK a (RepK (f a)), ArbitraryForAll as f)

type Yo e m = ArbitraryForAll (TypesOf (RepK e)) (e m)

------------------------------------------------------------------------------

debugEffGen :: forall e a m. (GArbitraryK a (RepK (e m a)), GenericK (e m a)) => Gen (e m a)
debugEffGen = fmap toK $ oneof $ garbitraryk @a @(RepK (e m a))

debugGen :: Yo CircleBuffer m => Gen (CircleBuffer m Int)
debugGen = debugEffGen

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
  getAParticularEffGen = (fmap SomeEff $ debugEffGen @e @a @(Sem r)) : getAParticularEffGen @as @e @r

instance GetAnEffGen '[] r where
  getAnEffGen = []

instance
    (GetAnEffGen es r, GetAParticularEffGen (TypesOf (RepK e)) e r)
    => GetAnEffGen (e ': es) r
    where
  getAnEffGen = fmap (fmap SomeSomeEff) (getAParticularEffGen @(TypesOf (RepK e)) @e @r)
             <> getAnEffGen @es @r


prop_writerStateComm :: Property
prop_writerStateComm =
  prepropCommutative @(State Int) @(State Int) @'[State Int, State Int] $ pure . run . evalState 0 . subsume



prepropCommutative
    :: forall e1 e2 r
     . ( GetAnEffGen r r
       , GetAnEffGen '[e1] r
       , GetAnEffGen '[e2] r
       )
    => (forall a. Sem r a -> IO a)
    -> Property
prepropCommutative lower = property @(Gen Property) $ do
  SomeSomeEff (SomeEff m) <- oneof $ getAnEffGen @r @r
  SomeSomeEff (SomeEff e1) <- oneof $ getAnEffGen @'[e1] @r
  SomeSomeEff (SomeEff e2) <- oneof $ getAnEffGen @'[e2] @r
  pure $
    counterexample "Effects are not commutative!" $
    counterexample "" $
    counterexample ("e1 = " <> show e1) $
    counterexample ("e2 = " <> show e2) $
    counterexample ("k  = " <> show m) $
    counterexample "" $
    counterexample "(e1 >> e2 >> k) /= (e2 >> e1 >> k)" $
    counterexample "" $
      ioProperty $ do
        r1 <- lower $ send e1 >> send e2 >> send m
        r2 <- lower $ send e2 >> send e1 >> send m
        pure $ r1 === r2



---


synthesizeAny
    :: forall e a m
     . (GArbitraryK a (RepK (e m a)), GenericK (e m a))
    => TypeRep a
    -> Maybe (Gen (e m a))
synthesizeAny _ =
  case garbitraryk @a @(RepK (e m a)) of
    [] -> Nothing
    a -> Just $ fmap toK $ oneof a


------------------------------------------------------------------------------

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


types :: Set ATypeRep
types = gtypesofk @(RepK CircleBuffer)

debugSet :: Set ATypeRep -> IO ()
debugSet = traverse_ $ \(ATypeRep tr) -> do
  case synthesizeAny @CircleBuffer tr of
    Nothing -> print "(impossible)"
    Just g -> generate g >>= print



-- test :: Property
-- test =
--   prepropEquivInterpreters @'[CircleBuffer] @Int
--       (runM . runCircleBuffer [] 5)
--       (pure . run . runCircleBufferSpec 5)
--     $ gen

gen :: Member CircleBuffer r => Gen (Sem r Int)
gen = oneof
  [ do
      n <- arbitrary
      k <- gen
      pure $ putE n >> k
  , pure getE
  , pure lenE
  ]


prepropLaw
    :: (Eq x, Show x)
    => Gen (Sem r a, Sem r a)
    -> (Sem r a -> IO x)
    -> Property
prepropLaw g lower = property $ do
  (m1, m2) <- g
  pure $ ioProperty $ do
    a1 <- lower m1
    a2 <- lower m2
    pure $ a1 === a2

stateLaw2
    :: forall s r x
     . (Eq x, Show x, Arbitrary s, Member (State s) r)
    => (Sem r () -> IO x)
    -> Property
stateLaw2 = prepropLaw $ do
  s1 <- arbitrary
  s2 <- arbitrary
  pure $
    ( do
        put @s s1
        put @s s2
    , do
        put @s s2
    )


------------------------------------------------------------------------------
-- | Make a string representation for a failing 'runLaw' property.
mkCounterexampleString
    :: Show a
    => String
    -> a
    -> String
    -> a
    -> [String]
    -> String
mkCounterexampleString str1 a str2 b args =
  mconcat
    [ printf str1 args , " (result: " , show a , ")\n /= \n"
    , printf str2 args , " (result: " , show b , ")"
    ]





prepropEquivInterpreters
    :: forall effs x r1 r2
     . (Eq x, Show x, Inject effs r1, Inject effs r2, Members effs effs)
    => (forall a. Sem r1 a -> IO a)
    -> (forall a. Sem r2 a -> IO a)
    -> (forall r. Members effs r => Gen (Sem r x))
    -> Property
prepropEquivInterpreters int1 int2 mksem = property $ do
  SomeSem sem <- liftGen @effs @x mksem
  pure $ ioProperty $ do
    a1 <- int1 sem
    a2 <- int2 sem
    pure $ a1 === a2

newtype SomeSem effs a = SomeSem
  { getSomeSem :: forall r. (Inject effs r) => Sem r a
  }

liftGen
    :: forall effs a
     . Members effs effs
    => (forall r. Members effs r => Gen (Sem r a))
    -> Gen (SomeSem effs a)
liftGen g = do
  a <- g @effs
  pure $ SomeSem $ inject a

inject :: Inject effs r => Sem effs a -> Sem r a
inject (Sem a) = a $ liftSem . deject . hoist inject

class Inject effs r where
  deject :: Union effs (Sem r) a -> Union r (Sem r) a

instance Inject '[] r where
  deject = absurdU

instance {-# INCOHERENT #-} Inject r r where
  deject = id

instance (Member eff r, Inject effs r) => Inject (eff ': effs) r where
  deject u =
    case decomp u of
      Left  u' -> deject u'
      Right w  -> Union membership w

