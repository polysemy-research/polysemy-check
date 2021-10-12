module Test where

import GHC.Generics
import Polysemy
import Polysemy.Check
import Test.QuickCheck


data Test m a where
  Test :: Show b => b -> Test m ()

deriving instance Show (Test m a)

makeSem ''Test
deriveGenericK ''Test


type LawConstraints f effs s r =
       ( Arbitrary s
       , Members effs r
       , Eq s
       , Show s
       , ArbitraryEff effs r
       , f ~ (,) s
       , effs ~ '[Test]
       )

blah :: IO (SomeAction Test '[Test])
blah = generate $ arbitraryAction @Test

-- putGetLaw
--     :: forall s r res effs f
--      . ( res ~ s
--        , LawConstraints f effs s r
--        )
--     => (forall a. Sem r (res, a) -> IO (f (res, a)))
--     -> Property
-- putGetLaw = prepropLaw @effs $ do
--   undefined
