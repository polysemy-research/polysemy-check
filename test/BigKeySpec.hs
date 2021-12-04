{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}

module BigKeySpec where

import qualified Data.Map as M
import Data.Map (Map)
import Polysemy
import Polysemy.Check
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck
import Polysemy.State
import Data.Functor.Identity
import Data.Word

data KVStore k v m a where
  Store :: k -> v -> KVStore k v m ()
  Delete :: k -> KVStore k v m ()
  Retrieve :: k -> KVStore k v m (Maybe v)

deriving instance (Show k, Show v) => Show (KVStore k v m a)

makeSem ''KVStore
deriveGenericK ''KVStore


data Bug = HasBug | NoBug

runKVStore :: forall k v r a. Ord k => Bug -> Sem (KVStore k v ': r) a -> Sem r a
runKVStore bug = (evalState (mempty @(Map k v)) .) $  reinterpret $ \case
  Store k v -> modify $ M.insert k v
  Delete k ->
    case bug of
      HasBug -> pure ()
      NoBug -> modify $ M.delete k
  Retrieve k -> gets $ M.lookup k


deleteGetLaw
    :: forall r
     . r ~ '[KVStore Word64 Bool]
    => Bug
    -> (Word64 -> Bool -> [Sem r ()])
    -> Property
deleteGetLaw bug prel =
  prepropLaw @r
    (do
      k <- arbitrary
      v <- arbitrary
      pure $ Law
        { lawLhs = do
            delete k
            retrieve k
        , lawRhs = do
            delete k
            pure Nothing
        , lawPrelude = prel k v
        , lawPostlude = [] :: [Sem r ()]
        }
    )
    Nothing  -- (Just $ constructorLabel . runIdentity)
    (pure . Identity . run . runKVStore @Word64 @Bool bug)


spec :: Spec
spec = modifyMaxSize (const 100000) $ do
  describe "without prelude" $ do
    prop "with bug"    $ deleteGetLaw HasBug $ \_ _ -> []
    prop "without bug" $ deleteGetLaw NoBug $ \_ _ -> []

  describe "with prelude" $ do
    prop "with bug"    $ expectFailure $ deleteGetLaw HasBug $ \k v -> [store k v]
    prop "without bug" $ deleteGetLaw NoBug $ \k v -> [store k v]

