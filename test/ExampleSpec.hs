{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}

module ExampleSpec where

import Control.Monad
import Data.Maybe (listToMaybe)
import Polysemy
import Polysemy.Check
import Polysemy.State
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck


data Stack s m a where
  Push      :: s -> Stack s m ()
  Pop       :: Stack s m (Maybe s)
  RemoveAll :: Stack s m ()
  Size      :: Stack s m Int

deriving instance Show s => Show (Stack s m a)
deriveGenericK ''Stack

makeSem ''Stack


spec :: Spec
spec = do
  describe "Laws" $ do
    let law x = prepropLaw @'[Stack Int] x $ pure . run . runStack []

    prop "push >> pop is pure" $ do
      law $ do
        s <- arbitrary
        pure
          ( push s >> pop
          , pure $ Just s
          )

    prop "pop >> push is id" $ do
      law $
        pure
          ( pop >>= maybe (pure ()) push
          , pure ()
          )

    prop "removeAll sets size to 0" $ do
      law $
        pure
          ( removeAll >> size
          , removeAll >> pure 0
          )

    prop "push increases size by 1" $ do
      law $ do
        s <- arbitrary
        pure
          ( push s >> size
          , fmap (+1) size <* push s
          )

    prop "pop decreases size by 1" $ do
      law $ do
        pure
          ( pop >> size
          , fmap (max 0 . subtract 1) size <* pop
          )


  describe "Equivalence" $ do
    let equiv b1 b2 =
          prepropEquivalent @'[Stack Int]
            (pure . run . runStack b1)
            (pure . run . runStack b2)

    prop "All interpreters are equivalent to itself" $ do
      bugs <- arbitrary
      pure $ equiv bugs bugs

    prop "DontRemove bug interpreter isn't equivalent to the correct version" $
      expectFailure $ equiv [DontRemove] []

    prop "PushTwice bug interpreter isn't equivalent to the correct version" $
      expectFailure $ equiv [PushTwice] []

    prop "The buggy interpreters are not equivalent to one another" $
      expectFailure $ equiv [PushTwice] [DontRemove]


data Bug
  = PushTwice
  | DontRemove
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance Arbitrary Bug where
  arbitrary = elements [minBound..maxBound]


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

