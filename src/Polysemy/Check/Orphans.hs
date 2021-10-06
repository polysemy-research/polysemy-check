{-# OPTIONS_GHC -Wno-orphans #-}

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

deriving instance Show s => Show (State s (Sem r) a)
deriving instance Show o => Show (Output o (Sem r) a)
deriving instance Show i => Show (Input i (Sem r) a)
deriving instance Show (Fail (Sem r) a)

instance Show e => Show (Error e (Sem r) a) where
  show (Throw e2) = "Throw " <> show e2
  show (Catch _ _) = "<catch>"

