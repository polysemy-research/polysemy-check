{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE QuantifiedConstraints #-}
module Polysemy.Check.Orphans () where

import Generics.Kind.TH
import Polysemy
import Polysemy.Error
import Polysemy.Fail
import Polysemy.Fixpoint
import Polysemy.Input
import Polysemy.NonDet
import Polysemy.Output
import Polysemy.Reader
import Polysemy.Resource
import Polysemy.State
import Polysemy.Tagged
import Polysemy.Trace
import Polysemy.View
import Polysemy.Writer
import Polysemy.Check.Arbitrary (Checkable(..))
import Test.QuickCheck (Arbitrary, CoArbitrary, arbitrary)

deriveGenericK ''Embed
deriveGenericK ''Error
deriveGenericK ''Fail
deriveGenericK ''Fixpoint
deriveGenericK ''Input
deriveGenericK ''NonDet
deriveGenericK ''Output
deriveGenericK ''Reader
deriveGenericK ''Resource
deriveGenericK ''State
deriveGenericK ''Tagged
deriveGenericK ''Trace
deriveGenericK ''View
deriveGenericK ''Writer

instance Arbitrary s => Checkable (State s)
instance Arbitrary s => Checkable (Output s)
instance (CoArbitrary s, Arbitrary s) => Checkable (Error s)
-- instance (CoArbitrary s, Arbitrary s) => Checkable (Writer s)
instance (Arbitrary s, CoArbitrary s) => Checkable (Reader s)
instance Checkable (Input i)
instance Checkable Fail
instance Checkable Trace
instance Checkable (Embed m) where
  hoistEff = undefined
  shrinkEff = undefined

instance Show (Embed m r a) where
  show _ = "yo"

instance Arbitrary (IO a) where
  arbitrary = undefined

deriving instance Show s => Show (State s m a)
deriving instance Show o => Show (Output o m a)
deriving instance Show (Input i m a)
deriving instance Show (Fail m a)
deriving instance Show (Trace m a)

instance (Show e, Show (m a)) => Show (Error e m a) where
  show (Throw e2) = "Throw " <> show e2
  show (Catch m _) = "Catch " <> show m <> " <k>"

instance Show (m a) => Show (Reader e m a) where
  show Ask = "Ask"
  show (Local _ m) = "Local <f> " <> show m

instance Show e => Show (Writer e m a) where
  show (Tell e) = "Tell " <> show e
  show (Listen _) = "Listen <m>"
  show (Pass _) = "Pass <m>"

