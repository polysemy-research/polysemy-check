module Lib where

import Orphans ()
import Polysemy
import Polysemy.Internal
import Polysemy.Internal.Union.Inject (Inject, inject)
import Polysemy.Law
import Polysemy.State
import Polysemy.Check.AnyEff


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


-- test :: Property
-- test =
--   prepropEquivInterpreters @'[CircleBuffer] @Int
--       (runM . runCircleBuffer [] 5)
--       (pure . run . runCircleBufferSpec 5)
--     $ gen

-- gen :: Member CircleBuffer r => Gen (Sem r Int)
-- gen = oneof
--   [ do
--       n <- arbitrary
--       k <- gen
--       pure $ putE n >> k
--   , pure getE
--   , pure lenE
--   ]


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

