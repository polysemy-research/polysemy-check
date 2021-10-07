module Polysemy.Check
  ( prepropCommutative
  , prepropEquivalent
  , prepropLaw
  , deriveGenericK
  ) where

import Generics.Kind.TH (deriveGenericK)
import Polysemy
import Polysemy.Check.AnyEff
import Polysemy.Check.Orphans ()
import Polysemy.Internal
import Polysemy.Internal.Union.Inject (Inject, inject)
import Test.QuickCheck


------------------------------------------------------------------------------
-- | Prove that two effects are commutative (a la
-- <https://dl.acm.org/doi/10.1145/3473578 Reasoning about effect interaction by fusion>)
-- under the given interpreter.
--
-- Humans naturally expect that disparate effects do not interact, thus
-- commutativity is an important property for reasoning about the correctness
-- of your program.
--
-- For example,
--
-- @
-- 'prepropCommutative' \@(State Int) \@Trace \@EffStack runEffStack
-- @
--
-- will interleave random @State Int@ and @Trace@ actions, within a bigger
-- context of @EffStack@ actions. The resulting 'Property' will fail if
-- permuting the @State Int@ and @Trace@ effects changes the outcome of the
-- entire computation.
prepropCommutative
    :: forall e1 e2 r
     . ( GetAnEffGen r r
       , GetAnEffGen '[e1] r
       , GetAnEffGen '[e2] r
       )
    => (forall a. Sem r a -> IO a)
    -> Property
prepropCommutative lower = property @(Gen Property) $ do
  SomeSomeEff (SomeEff m1) <- oneof $ getAnEffGen @r @r
  SomeSomeEff (SomeEff e1) <- oneof $ getAnEffGen @'[e1] @r
  SomeSomeEff (SomeEff e2) <- oneof $ getAnEffGen @'[e2] @r
  SomeSomeEff (SomeEff m2) <- oneof $ getAnEffGen @r @r
  pure $
    counterexample "Effects are not commutative!" $
    counterexample "" $
    counterexample ("k1  = " <> show m1) $
    counterexample ("e1 = " <> show e1) $
    counterexample ("e2 = " <> show e2) $
    counterexample ("k2  = " <> show m2) $
    counterexample "" $
    counterexample "(e1 >> e2 >> k) /= (e2 >> e1 >> k)" $
    counterexample "" $
      ioProperty $ do
        r1 <- lower $ send m1 >> send e1 >> send e2 >> send m2
        r2 <- lower $ send m1 >> send e2 >> send e1 >> send m2
        pure $ r1 === r2


------------------------------------------------------------------------------
-- | Prove that two programs in @r@ are equivalent under a given
-- interpretation. This is useful for proving laws about particular effects (or
-- stacks of effects).
--
-- For example, any lawful interpretation of @State@ must satisfy the @put s1
-- >> put s2 = put s2@ law.
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


------------------------------------------------------------------------------
-- | Prove that two interpreters are equivalent. For the given generator, this
-- property ensures that the two interpreters give the same result for every
-- arbitrary program.
prepropEquivalent
    :: forall effs x r1 r2
     . (Eq x, Show x, Inject effs r1, Inject effs r2, Members effs effs)
    => (forall a. Sem r1 a -> IO a)
    -> (forall a. Sem r2 a -> IO a)
    -> (forall r. Members effs r => Gen (Sem r x))
    -> Property
prepropEquivalent int1 int2 mksem = property $ do
  SomeSem sem <- liftGen @effs @x mksem
  pure $ ioProperty $ do
    a1 <- int1 sem
    a2 <- int2 sem
    pure $ a1 === a2


newtype SomeSem effs a = SomeSem
  { _getSomeSem :: forall r. (Inject effs r) => Sem r a
  }


liftGen
    :: forall effs a
     . Members effs effs
    => (forall r. Members effs r => Gen (Sem r a))
    -> Gen (SomeSem effs a)
liftGen g = do
  a <- g @effs
  pure $ SomeSem $ inject a

