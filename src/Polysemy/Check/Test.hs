{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Polysemy.Check.Test where

import Polysemy
import Polysemy.Output
import Polysemy.Check
import Polysemy.Internal
import Polysemy.Internal.Union
import Test.QuickCheck hiding (output)
import Polysemy.Error
import Polysemy.Input
import Polysemy.State
import Data.Foldable (for_)
import Debug.RecoverRTTI

-- class RaiseEnd effs end where
--   smaiseEnd :: Union effs (Sem (Append effs end)) a -> Union (Append effs end) (Sem (Append effs end)) a

-- instance RaiseEnd '[] end where
--   smaiseEnd = absurdU

-- instance RaiseEnd es end => RaiseEnd (e ': es) end where
--   smaiseEnd (Union n w) = Union (undefined n) w

-- raiseEnd :: forall effs end a. RaiseEnd effs end => Sem effs a -> Sem (Append effs end) a
-- raiseEnd (Sem a) = a $ liftSem . smaiseEnd @effs @end . hoist (raiseEnd @effs @end)


-- instance {-# OVERLAPPING #-}
--          (Show a, Arbitrary a, ArbitraryEff r r, ArbitraryEffOfType a r r, res ~ Append r '[Output String], RaiseEnd r '[Output String])
--       => Arbitrary (Sem res a) where
--   arbitrary =
--     let terminal =
--           [ do
--               a <- arbitrary
--               pure $ do
--                 -- output $ "pure " <> show a
--                 pure a
--           ]
--      in sized $ \n ->
--           case n <= 1 of
--             True -> oneof terminal
--             False -> frequency $
--               [ (2,) $ do
--                   SomeEffOfType e <- arbitraryActionFromRowOfType @r @r @a
--                   pure $ do
--                     -- output $ show e
--                     raiseEnd @r @'[Output String] $ send e
--               , (8,) $ do
--                   SomeEff e <- arbitraryActionFromRow @r @r
--                   k <- scale (`div` 2) (arbitrary @(Fun _ (Sem (Append r '[Output String]) a)))
--                   pure $ do
--                     -- output $ show e <> " >>= k"
--                     raiseEnd @r @'[Output String] (send e) >>= applyFun k
--               ] <> fmap (1,) terminal
--   shrink _ = []


test :: IO ()
test = do
  a <- generate $ arbitrary @(Sem '[Input Bool, State Int] Int)
  let (x, _) =
        run . evalState 0 . runInputConst True $ debugShow  a

  for_ x putStrLn




debugShow :: Sem r a -> Sem r ([String], a)
debugShow = runOutputList . watch (output . anythingToString) . raise


watch
    :: (forall (e :: Effect) m x. e m x -> Sem r ())
    -> Sem r a
    -> Sem r a
watch f (Sem m) = Sem $ \k -> m $ \u ->
  case u of
    Union _ (Weaving e _ _ _ _) -> do
        usingSem k $ f e
        k $ hoist (watch f) u

