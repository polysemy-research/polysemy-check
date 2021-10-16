{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}

module ExampleSpec where

import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.Hspec.QuickCheck
import Polysemy.State
import Control.Monad
import Data.Maybe (listToMaybe)
import Test.QuickCheck (expectFailure, arbitrary, elements)
import GHC.Generics (Generic)
import Test.QuickCheck.Arbitrary (Arbitrary)


data Stack s m a where
  Push      :: s -> Stack s m ()
  Pop       :: Stack s m (Maybe s)
  RemoveAll :: Stack s m ()
  Size      :: Stack s m Int

deriving instance Show s => Show (Stack s m a)
deriveGenericK ''Stack


spec :: Spec
spec = do
  prop "An interpreter is equivalent to itself" $ do
    bugs <- arbitrary
    pure $
      prepropEquivalent @'[Stack Int] @Int
        (pure . run . runStack bugs)
        (pure . run . runStack bugs)
  prop "DontRemove bug interpreter isn't equivalent to the correct version" $
    expectFailure $
      prepropEquivalent @'[Stack Int] @Int
        (pure . run . runStack [DontRemove])
        (pure . run . runStack [])
  prop "PushTwice bug interpreter isn't equivalent to the correct version" $
    expectFailure $
      prepropEquivalent @'[Stack Int] @Int
        (pure . run . runStack [PushTwice])
        (pure . run . runStack [])
  prop "The buggy interpreters are not equivalent to one another" $
    expectFailure $
      prepropEquivalent @'[Stack Int] @Int
        (pure . run . runStack [PushTwice])
        (pure . run . runStack [DontRemove])


data Bug
  = PushTwice
  | DontRemove
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)

instance Arbitrary Bug where
  arbitrary = elements [PushTwice, DontRemove]


hasBug :: [Bug] -> Bug -> Bool
hasBug = flip elem


runStack
    :: [Bug]
    -> Sem (Stack s ': r) a
    -> Sem r ([s], a)
runStack bugs =
  (runState [] .) $ reinterpret $ \case
    Push s -> do
      modify (s :)
      when (hasBug bugs PushTwice) $
        modify (s :)
    Pop -> do
      r <- gets listToMaybe
      modify (drop 1)
      pure r
    RemoveAll ->
      unless (hasBug bugs DontRemove) $
        put []
    Size -> gets length

