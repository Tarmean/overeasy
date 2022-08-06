{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module Overeasy.Pending (Pending(..), pendingNew, pendingMarkKnown, pendingFinished) where

import qualified Data.Set as S
import qualified Data.Map as M
-- Probaby should use IntLikeMap/Set for consistency, but they don't offer some methods like fromListWith

import Control.Monad.State
    ( gets, modify, MonadState(state), StateT, execStateT )
import Control.Monad.Writer
    ( runWriter, MonadWriter(tell), Writer )
import Control.Monad (filterM)

data Pending cls nod = Pending {
   -- | How many children are unknown - when this becomes 0, propagate.
   -- When a child occurs multiple times it only counts once
   pendingUnknownCount :: M.Map nod Int,
   -- | Backmap of children to parents
   pendingParents :: M.Map cls (S.Set nod)
} deriving (Eq, Ord, Show)

pendingNew :: (Ord cls, Ord nod) => M.Map nod (S.Set cls) -> (Pending cls nod, S.Set nod)
pendingNew argMap = (Pending childCounts revMap , trivial)
  where
    childCounts0 = M.map S.size argMap
    (trivialMap, childCounts) = M.partition (==0) childCounts0
    trivial = S.fromList (M.keys trivialMap)

    revMap = M.fromListWith S.union $ do
      (parent, children) <- M.toList argMap
      child <- S.toList children
      return (child, S.singleton parent)


pendingFinished :: (Ord cls, Ord nod) => Pending cls nod -> Bool
pendingFinished = M.null . pendingUnknownCount


test1 :: M.Map Integer (S.Set Integer)
test1 = M.fromList [(1, S.fromList [2, 3]), (2, S.fromList [3, 4]), (3, S.fromList [4, 5])]

type M cls nod = StateT (Pending cls nod) (Writer (S.Set nod))

-- | Set the 'learned' elements as known, and propagate.
-- Returns the set of elements that were learned by propagation
-- The original 'learned' is part of the input if they weren't done before
pendingMarkKnown :: (Ord nod, Ord cls) => [cls] -> Pending cls nod -> (Pending cls nod, S.Set nod)
pendingMarkKnown learned s = runWriter (execStateT (mapM_ go learned) s)
  where
    go :: (Ord nod, Ord cls) =>  cls -> M cls nod ()
    go x = do
        occurences <- popOccurences x
        newlyUnblocked <- filterM tryUnblockParent (S.toList occurences)
        tell (S.fromList newlyUnblocked )
        -- unblockedClasses <- mapM toClass newlyUnblocked
        -- go (unblockedClasses <> queue)

toClass :: nod -> M cls nod cls
toClass = error "not implemented"

tryUnblockParent :: Ord nod => nod -> M cls nod Bool
tryUnblockParent a = do
    getUnknownChildren a >>= \case
          Nothing -> pure False
          Just 1 -> do
            modify $ updateUnknownChildren (const Nothing) a
            pure True
          Just _ -> do
            modify $ updateUnknownChildren (\x -> Just (x-1)) a
            pure False


popOccurences :: (Ord nod, Ord cls) => cls -> M cls nod (S.Set nod)
popOccurences cls = state (extractOccurences cls)

getUnknownChildren :: Ord nod => nod -> M cls nod (Maybe Int)
getUnknownChildren a = gets (M.lookup a . pendingUnknownCount)

updateUnknownChildren :: Ord nod => (Int -> Maybe Int) -> nod -> Pending cls nod -> Pending cls nod
updateUnknownChildren f k Pending { pendingUnknownCount, .. } = Pending { pendingUnknownCount = M.update f k pendingUnknownCount, .. }

extractOccurences :: (Ord cls) =>cls -> Pending cls nod -> (S.Set nod, Pending cls nod)
extractOccurences k Pending {pendingParents, ..} = (out, Pending {pendingParents = parents', ..})
  where
    parents' = M.delete k pendingParents
    out = M.findWithDefault S.empty k pendingParents
