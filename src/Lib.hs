module Lib where

import Polysemy
import Polysemy.Check
import Polysemy.Check.Orphans ()
import Polysemy.State
import Test.QuickCheck


prop_writerStateComm :: Property
prop_writerStateComm =
  prepropCommutative @(State Int) @(State Int) @'[State Int, State Int] $ pure . run . evalState 0 . subsume


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

