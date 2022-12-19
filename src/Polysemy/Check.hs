{-# LANGUAGE QuantifiedConstraints #-}

module Polysemy.Check
  ( -- * Effect Properties
    prepropCommutative
  , prepropAllCommutative
  , prepropEquivalent
  , prepropLaw

    -- * Law Constructors
  , Law (..)
  , simpleLaw

    -- * Generators for Effects
  , arbitraryAction
  , arbitraryActionOfType
  , arbitraryActionFromRow
  , arbitraryActionFromRowOfType

    -- * Types for Generators for Effects
  , SomeAction (..)
  , SomeEff (..)
  , SomeEffOfType (..)

  -- * Common labeling functions
  , constructorLabel

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
import Polysemy.Internal.Union.Inject (Inject, inject)
import Test.QuickCheck
import Data.Data (Data, showConstr, toConstr)


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
prepropCommutative lower = property @(Gen Property) $ do
  SomeEff m1 <- arbitraryActionFromRow @r @r
  SomeEff e1 <- arbitraryActionFromRow @effs1 @r
  SomeEff e2 <- arbitraryActionFromRow @effs2 @r
  SomeEff m2 <- arbitraryActionFromRow @r @r
  pure $
    counterexample "Effects are not commutative!" $
    counterexample "" $
    counterexample ("k1  = " <> show m1) $
    counterexample ("e1 = " <> show e1) $
    counterexample ("e2 = " <> show e2) $
    counterexample ("k2  = " <> show m2) $
    counterexample "" $
    counterexample "(k1 >> e1 >> e2 >> k2) /= (k1 >> e2 >> e1 >> k2)" $
      ioProperty $ do
        r1 <- lower $ send m1 >> send e1 >> send e2 >> send m2
        r2 <- lower $ send m1 >> send e2 >> send e1 >> send m2
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
-- | Data structure containing programs that should be equal, and under which
-- circumstances.
--
-- @since 0.9.0.0
data Law r z a = Law
  { lawLhs      :: Sem r a
    -- ^ 'lawLhs' and 'lawRhs' are being asserted as equal.
  , lawRhs      :: Sem r a
    -- ^ 'lawLhs' and 'lawRhs' are being asserted as equal.
  , lawPrelude  :: [Sem r ()]
    -- ^ A set of actions to possibly run before checking equality. Useful for
    -- ensuring the existence of something being tested.
  , lawPostlude :: [Sem r z]
    -- ^ A set of actions to possibly run after checking equality. Useful for
    -- checking the existence after something was created.
  }


------------------------------------------------------------------------------
-- | Like 'Law', but for the common case when you don't need a custom prelude
-- or postlude.
--
-- @since 0.9.0.0
simpleLaw :: Sem r a -> Sem r a -> Law r () a
simpleLaw lhs rhs = Law lhs rhs [] []


------------------------------------------------------------------------------
-- | Prove that two programs in @r@ are equivalent under a given
-- interpretation. This is useful for proving laws about particular effects (or
-- stacks of effects).
--
-- For example, any lawful interpretation of @State@ must satisfy the @put s1
-- >> put s2 = put s2@ law.
prepropLaw
    :: forall effs x r a f
     . ( (forall z. Eq z => Eq (f z))
       , (forall z. Show z => Show (f z))
       )
    => ( Eq a
       , Show a
       , Functor f
       , ArbitraryEff effs r
       , Eq x
       , Show x
       )
    => Gen (Law r x a)
       -- ^ A generator for two equivalent programs.
    -> Maybe (f a -> String)
       -- ^ How to label the results for QuickCheck coverage.
    -> (forall z. Sem r (a, z) -> IO (f (a, z)))
       -- ^ An interpreter for the effect stack down to 'IO'. Pure effect
       -- stacks can be lifted into 'IO' via 'pure' after the final 'run'.
    -> Property
prepropLaw g labeler lower = property @(Gen Property) $ do
  Law lhs rhs mprel mpost <- g
  SomeEff pre1 <- arbitraryActionFromRow @effs @r
  prel <- maybeOneof mprel
  SomeEff pre2 <- arbitraryActionFromRow @effs @r
  SomeEff post1 <- arbitraryActionFromRow @effs @r
  post <- maybeOneof mpost
  SomeEff post2 <- arbitraryActionFromRow @effs @r
  pure $
    counterexample ("before1 = " <> show pre1) $
    counterexample ("before2 = " <> show pre2) $
    counterexample ("after1  = " <> show post1) $
    counterexample ("after2  = " <> show post2) $
      ioProperty $ do
        a1 <-
          lower $ do
            void $ send pre1
            void $ prel
            void $ send pre2
            a1 <- lhs
            void $ send post1
            z <- post
            r <- send post2
            pure (a1, (z, r))
        a2 <-
          lower $ do
            void $ send pre1
            void prel
            void $ send pre2
            a2 <- rhs
            void $ send post1
            z <- post
            r <- send post2
            pure (a2, (z, r))
        pure
          $ maybe property (\lbl -> label $ lbl $ fmap fst a1) labeler
          $ a1 === a2


maybeOneof :: [Sem r a] -> Gen (Sem r (Maybe a))
maybeOneof [] = pure $ pure Nothing
maybeOneof res = do
  chance <- elements @Int [0..9]
  case chance < 8 of
    True -> fmap (fmap Just) $ elements res
    False -> pure $ pure Nothing



------------------------------------------------------------------------------
-- | Label an example with its data constructor.
--
-- @since 0.9.0.0
constructorLabel :: Data a => a -> String
constructorLabel = showConstr . toConstr


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

