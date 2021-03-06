module Polysemy.Internal.Union.Inject
  ( inject
  , Inject
  ) where

import Polysemy.Internal
import Polysemy.Internal.Union


------------------------------------------------------------------------------
-- | Morally:
--
-- @
-- 'inject' :: 'Members' effs r => 'Sem' effs a -> 'Sem' r a
-- @
inject :: Inject effs r => Sem effs a -> Sem r a
inject (Sem a) = a $ liftSem . deject . hoist inject


------------------------------------------------------------------------------
-- | Helper class for munging the 'Union' so that we can implement 'inject'.
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

