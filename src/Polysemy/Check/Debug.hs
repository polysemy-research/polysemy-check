{-# OPTIONS_GHC -Wno-orphans #-}

module Polysemy.Check.Test where

import Polysemy
import Polysemy.Output
import Polysemy.Internal
import Polysemy.Internal.Union
import Debug.RecoverRTTI
import Polysemy.Writer
import Polysemy.Input
import Polysemy.State
import Polysemy.Check
import Test.QuickCheck
import Data.Foldable (for_)
import Polysemy.Internal.Union.Inject (inject)
import Polysemy.Error
import Polysemy.Reader


data DebugEffect
  = CallEffect String Bool [DebugEffect]
  deriving (Eq, Ord, Show)


prettyDebugEffect :: DebugEffect -> String
prettyDebugEffect (CallEffect s _ []) = s
prettyDebugEffect (CallEffect s _ ds) = unlines $
  s : fmap (mappend "  " . prettyDebugEffect) ds

filterDebugEffect :: [DebugEffect] -> [DebugEffect]
filterDebugEffect [] = []
filterDebugEffect (CallEffect e1 False _ : CallEffect e2 True ds2 : xs)
  | e1 == e2
  = CallEffect e2 True (filterDebugEffect ds2) : filterDebugEffect xs
filterDebugEffect (CallEffect e b ds : xs) = CallEffect e b (filterDebugEffect ds) : filterDebugEffect xs



test :: IO ()
test = do
  a <- generate $ arbitrary @(Sem '[Reader Int, Input Bool, State Int] Int)
  let (x, _) =
        run . runWriter @[DebugEffect] . runReader @Int 5 . evalState (0 :: Int) . runInputConst True $ watch $ inject a

  for_ (filterDebugEffect x) $ putStrLn . prettyDebugEffect

watch
    :: Member (Writer [DebugEffect]) r
    => Sem r a
    -> Sem r a
watch (Sem m) = Sem $ \k -> m $ \u ->
  case u of
    Union _ (Weaving e _ _ _ _) -> do
      usingSem k $ do
        tell [CallEffect (anythingToString e) False []]
        (x, r) <- send $ Listen @[DebugEffect] $ liftSem $ hoist watch u
        tell [CallEffect (anythingToString e) True x]
        pure r

