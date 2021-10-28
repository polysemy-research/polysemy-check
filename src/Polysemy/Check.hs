{-# LANGUAGE QuantifiedConstraints #-}

module Polysemy.Check
  ( -- * Effect Properties
    prepropCommutative
  , prepropAllCommutative
  , prepropEquivalent
  , prepropLaw

    -- * Generators for Effects
  , arbitraryAction
  , arbitraryActionOfType
  , arbitraryActionFromRow
  , arbitraryActionFromRowOfType

    -- * Types for Generators for Effects
  , SomeAction (..)
  , SomeEff (..)
  , SomeEffOfType (..)

    -- * Support for Existential Types
  , ExistentialFor

    -- * Constraints for Generators of Effects
  , GArbitraryK
  , ArbitraryAction
  , ArbitraryEff
  , ArbitraryEffOfType
  , TypesOf

    -- * Re-exports
  , send
  , deriveGenericK
  , GenericK
  ) where

import Control.Monad (void)
import Generics.Kind (GenericK)
import Generics.Kind.TH (deriveGenericK)
import Polysemy
import Polysemy.Check.Arbitrary
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
-- 'prepropCommutative' \@'[State Int] \@'[Trace] \@EffStack runEffStack
-- @
--
-- will interleave random @State Int@ and @Trace@ actions, within a bigger
-- context of @EffStack@ actions. The resulting 'Property' will fail if
-- permuting the @State Int@ and @Trace@ effects changes the outcome of the
-- entire computation.
prepropCommutative
    :: forall effs1 effs2 r f
     . ( forall a. Show a => Show (f a)
       , forall a. Eq a => Eq (f a)
       )
    => ( ArbitraryEff r r
       , ArbitraryEff effs1 r
       , ArbitraryEff effs2 r
       )
    => (forall a. Sem r a -> IO (f a))
       -- ^ An interpreter for the effect stack down to 'IO'. Pure effect
       -- stacks can be lifted into 'IO' via 'pure' after the final 'run'.
    -> Property
prepropCommutative lower =
  forAllP' @_ @Property (arbitraryActionFromRow @r @r) $ \(SomeEff m1) ->
  forAllP' @_ @Property (arbitraryActionFromRow @r @r) $ \(SomeEff m2) ->
  forAllP' @_ @Property (arbitraryActionFromRow @effs1 @r) $ \(SomeEff e1) ->
  forAllP' @_ @Property (arbitraryActionFromRow @effs2 @r) $ \(SomeEff e2) -> do
  counterexample "Effects are not commutative!" $
    counterexample "" $
    counterexample ("k1  = " <> show m1) $
    counterexample ("e1 = " <> show e1) $
    counterexample ("e2 = " <> show e2) $
    counterexample ("k2  = " <> show m2) $
    counterexample "" $
    counterexample "(k1 >> e1 >> e2 >> k2) /= (k1 >> e2 >> e1 >> k2)" $
      ioProperty $ do
        r1 <- lower $ send (hoistEff m1) >> send (hoistEff e1) >> send (hoistEff e2) >> send (hoistEff m2)
        r2 <- lower $ send (hoistEff m1) >> send (hoistEff e2) >> send (hoistEff e1) >> send (hoistEff m2)
        pure $ r1 === r2


class AllCommutative (effs :: EffectRow) r where
  ----------------------------------------------------------------------------
  -- | @'prepropAllCommutative' \@effs \@r interpreter@ generates an invocation
  -- of 'prepropCommutative' for every tail in @effs@. In essence, this ensures
  -- that every effect in @effs@ commutes with every other one.
  prepropAllCommutative
      :: ( forall a. Show a => Show (f a)
         , forall a. Eq a => Eq (f a)
         , Members effs r
         )
      => (forall a. Sem r a -> IO (f a))
      -> [Property]

instance {-# OVERLAPPING #-} AllCommutative '[e] r where
  prepropAllCommutative _ = []

instance (ArbitraryEff r r, ArbitraryEff es r, ArbitraryEff '[e] r, AllCommutative es r)
      => AllCommutative (e ': es) r where
  prepropAllCommutative lower
    = prepropCommutative @'[e] @es @r lower
    : prepropAllCommutative @es @r lower


------------------------------------------------------------------------------
-- | Prove that two programs in @r@ are equivalent under a given
-- interpretation. This is useful for proving laws about particular effects (or
-- stacks of effects).
--
-- For example, any lawful interpretation of @State@ must satisfy the @put s1
-- >> put s2 = put s2@ law.
prepropLaw
    :: forall effs r a f
     . ( (forall z. Eq z => Eq (f z))
       , (forall z. Show z => Show (f z))
       )
    => ( Eq a
       , Show a
       , ArbitraryEff effs r
       )
    => Gen (Sem r a, Sem r a)
       -- ^ A generator for two equivalent programs.
    -> (forall z. Sem r (a, z) -> IO (f (a, z)))
       -- ^ An interpreter for the effect stack down to 'IO'. Pure effect
       -- stacks can be lifted into 'IO' via 'pure' after the final 'run'.
    -> Property
prepropLaw g lower = property @(Gen Property) $ do
  SomeEff pre <- arbitraryActionFromRow @effs @r
  (m1, m2) <- g
  SomeEff post <- arbitraryActionFromRow @effs @r
  pure $
    counterexample ("before = " <> show pre) $
    counterexample ("after  = " <> show post) $
      ioProperty $ do
        a1 <-
          lower $ do
            void $ send $ hoistEff pre
            a1 <- m1
            r <- send $ hoistEff post
            pure (a1, r)
        a2 <-
          lower $ do
            void $ send $ hoistEff pre
            a2 <- m2
            r <- send $ hoistEff post
            pure (a2, r)
        pure $ a1 === a2


------------------------------------------------------------------------------
-- | Prove that two interpreters are equivalent. This property ensures that the
-- two interpreters give the same result for every arbitrary program.
prepropEquivalent
    :: forall effs r1 r2 f
     . ( forall a. Show a => Show (f a)
       , forall a. Eq a => Eq (f a)
       )
    => ( Inject effs r1
       , Inject effs r2
       , Arbitrary (Sem effs Int)
       )
    => (forall a. Sem r1 a -> IO (f a))
       -- ^ The first interpreter for the effect stack.Pure effect stacks can
       -- be lifted into 'IO' via 'pure' after the final 'run'.
    -> (forall a. Sem r2 a -> IO (f a))
       -- ^ The second interpreter to prove equivalence for.
    -> Property
prepropEquivalent int1 int2 = property $ do
  SomeSem sem <- liftGen @effs @Int
  pure $ ioProperty $ do
    a1 <- int1 sem
    a2 <- int2 sem
    pure $ a1 === a2


newtype SomeSem effs a = SomeSem
  { _getSomeSem :: forall r. (Inject effs r) => Sem r a
  }


liftGen
    :: forall effs a
     . Arbitrary (Sem effs a)
    => Gen (SomeSem effs a)
liftGen = do
  a <- arbitrary @(Sem effs a)
  pure $ SomeSem $ inject a

