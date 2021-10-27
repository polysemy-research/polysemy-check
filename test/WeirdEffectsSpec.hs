{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -ddump-tc-trace #-}

module WeirdEffectsSpec where

import Data.Typeable
import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Generics.Kind


data MyEffect (m :: * -> *) a where
  -- | Here, @e@ is existential!
  CanShow :: (Show e, Typeable e) => e -> MyEffect m ()

makeSem ''MyEffect

deriving instance Show (MyEffect m a)
deriveGenericK ''MyEffect


------------------------------------------------------------------------------
-- | When we synthesize a @MyEffect@ action, we instantiate all existentials at
-- @'ExistentialFor' MyEffect@.
--
-- This type must satisfy all of the constraints required by @CanShow@.
data instance ExistentialFor MyEffect = Hello
  deriving (Eq, Show)

-- It also requires an 'Arbitrary' instance!
instance Arbitrary (ExistentialFor MyEffect) where
  arbitrary = pure Hello


spec :: Spec
spec = do
  prop @(Gen Expectation) "Existentials get instantiated at 'ExistentialFor MyEffect'" $ do
    SomeAction e <- arbitraryAction @MyEffect @'[MyEffect]
    pure $ case e of
      CanShow t ->
        cast t `shouldBe` Just Hello




