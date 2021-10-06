module Polysemy.Internal.Union.Inject (Inject, inject) where

import Polysemy.Internal
import Polysemy.Internal.Union


inject :: Inject effs r => Sem effs a -> Sem r a
inject (Sem a) = a $ liftSem . deject . hoist inject

class Inject effs r where
  deject :: Union effs (Sem r) a -> Union r (Sem r) a

instance Inject '[] r where
  deject = absurdU

instance Inject r r where
  deject = id

instance (Member eff r, Inject effs r) => Inject (eff ': effs) r where
  deject u =
    case decomp u of
      Left  u' -> deject u'
      Right w  -> Union membership w

