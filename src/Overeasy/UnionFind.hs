{-# LANGUAGE DeriveAnyClass #-}

-- | A Union-Find implementation.
-- Not the best - requires at least 2 lookups to find the root.
-- But at least it's a persistent impl, and it compresses paths as it goes.
module Overeasy.UnionFind
  ( ufOnConflict
  , UnionFind
  , ufSize
  , ufTotalSize
  , ufNew
  , ufMembers
  , ufMembersRestricted
  , ufEquiv
  , ufEquivRestricted
  , ufRoots
  , ufAdd
  , ufFind
  , ufPartialFind
  , MergeRes (..)
  , ufMerge
  , MergeManyRes (..)
  , ufMergeMany
  ) where

import Control.DeepSeq (NFData)
import Control.Monad.State.Strict (State, modify', state)
import Data.Coerce (Coercible, coerce)
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Overeasy.IntLike.Equiv (IntLikeEquiv)
import qualified Overeasy.IntLike.Equiv as ILE
import Overeasy.IntLike.Map (IntLikeMap)
import qualified Overeasy.IntLike.Map as ILM
import Overeasy.IntLike.MultiMap (IntLikeMultiMap)
import qualified Overeasy.IntLike.MultiMap as ILMM
import Overeasy.IntLike.Set (IntLikeSet)
import qualified Overeasy.IntLike.Set as ILS

-- | Our default choice for merging class ids.
ufOnConflict :: Ord x => x -> x -> x
ufOnConflict = min
{-# INLINE ufOnConflict #-}

-- private ctor
data UnionFind x = UnionFind
  { ufSize :: !Int  -- ^ How many classes are there?
  , ufParents :: !(IntLikeMap x x)
  } deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

-- | How many discrete members have ever been added? (Number of classes via 'ufSize' is always LTE total.)
ufTotalSize :: UnionFind x -> Int
ufTotalSize = ILM.size . ufParents

-- | Creates a new UF
ufNew :: UnionFind x
ufNew = UnionFind 0 ILM.empty

-- private
ufMembersInc :: (Coercible x Int, Eq x) => UnionFind x -> (IntLikeMultiMap x x, UnionFind x)
ufMembersInc u@(UnionFind _ p) = ufMembersRestrictedInc (ILM.keys p) u

-- | Enumerates the members of the UF per-class (keys are roots)
ufMembers :: (Coercible x Int, Eq x) => State (UnionFind x) (IntLikeMultiMap x x)
ufMembers = state ufMembersInc

ufMembersRestrictedInc :: (Coercible x Int, Eq x) => [x] -> UnionFind x -> (IntLikeMultiMap x x, UnionFind x)
ufMembersRestrictedInc mems u = foldr go (ILM.empty, u) mems where
  go x1 (m, v) =
    let (x2, v') = ufFindRootInc x1 v
        m' = ILMM.insert x2 x1 m
    in (m', v')

ufMembersRestricted :: (Coercible x Int, Eq x) => [x] -> State (UnionFind x) (IntLikeMultiMap x x)
ufMembersRestricted = state . ufMembersRestrictedInc

ufEquivInc :: (Coercible x Int, Eq x) => UnionFind x -> (IntLikeEquiv x x, UnionFind x)
ufEquivInc u@(UnionFind _ p) = ufEquivRestrictedInc (ILM.keys p) u

ufEquiv :: (Coercible x Int, Eq x) => State (UnionFind x) (IntLikeEquiv x x)
ufEquiv = state ufEquivInc

ufEquivRestrictedInc :: (Coercible x Int, Eq x) => [x] -> UnionFind x -> (IntLikeEquiv x x, UnionFind x)
ufEquivRestrictedInc mems u = foldr go (ILE.empty, u) mems where
  go x1 (m, v) =
    let (x2, v') = ufFindRootInc x1 v
    in case ILE.insert x2 x1 m of
      Left _ -> error "UF equiv failure"
      Right m' -> (m', v')

ufEquivRestricted :: (Coercible x Int, Eq x) => [x] -> State (UnionFind x) (IntLikeEquiv x x)
ufEquivRestricted = state . ufEquivRestrictedInc

-- private
ufRootsInc :: (Coercible x Int, Eq x) => UnionFind x -> (IntLikeSet x, UnionFind x)
ufRootsInc u@(UnionFind _ p) = foldr go (ILS.empty, u) (ILM.keys p) where
  go x1 (s, v) =
    let (x2, v') = ufFindRootInc x1 v
        s' = ILS.insert x2 s
    in (s', v')

-- | Enumerates the roots of the UF
ufRoots :: (Coercible x Int, Eq x) => State (UnionFind x) (IntLikeSet x)
ufRoots = state ufRootsInc

-- private
ufAddInc :: Coercible x Int => x -> UnionFind x -> UnionFind x
ufAddInc x u@(UnionFind z p) =
  if ILM.member x p
    then u
    else UnionFind (z + 1) (ILM.insert x x p)

-- | Adds a new member to the UF
ufAdd :: Coercible x Int => x -> State (UnionFind x) ()
ufAdd = modify' . ufAddInc

-- private
ufFindRootAcc :: (Coercible x Int, Eq x) => IntLikeMap x x -> [x] -> x -> ([x], x)
ufFindRootAcc p acc x1 =
  -- partial: should exist in map by construction (all xs added in ufAddInc)
  let x2 = ILM.partialLookup x1 p
  in if x1 == x2
    then (acc, x2)
    else ufFindRootAcc p (x1:acc) x2

-- private
ufFindRootInc :: (Coercible x Int, Eq x) => x -> UnionFind x -> (x, UnionFind x)
ufFindRootInc x1 u@(UnionFind z p) =
  let (acc, x2) = ufFindRootAcc p [] x1
      u' = case acc of
            [] -> u
            _ -> let p' = foldr (`ILM.insert` x2) p acc
                 in UnionFind z p'
  in (x2, u')

-- private
ufFindInc :: (Coercible x Int, Eq x) => x -> UnionFind x -> (Maybe x, UnionFind x)
ufFindInc a u@(UnionFind _ p) =
  case ILM.lookup a p of
    Nothing -> (Nothing, u)
    Just x ->
      let (y, u') = ufFindRootInc x u
      in (Just y, u')

-- | Finds the canonical class member of the UF or 'Nothing' if not found
ufFind :: (Coercible x Int, Eq x) => x -> State (UnionFind x) (Maybe x)
ufFind x = state (ufFindInc x)

-- | Finds the canonical class member of the UF or calls 'error'.
-- NOTE: THIS IS PARTIAL!
ufPartialFind :: (Coercible x Int, Eq x) => x -> State (UnionFind x) x
ufPartialFind x = fmap (fromMaybe (error ("Could not find in UF: " ++ show (coerce x :: Int)))) (ufFind x)

-- | The result of trying to merge two elements of the 'UnionFind'
data MergeRes x =
    MergeResMissing !x
  | MergeResUnchanged !x
  | MergeResChanged !x
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic)
  deriving anyclass (NFData)

-- private
ufMergeInc :: (Coercible x Int, Ord x) => x -> x -> UnionFind x -> (MergeRes x, UnionFind x)
ufMergeInc i j u@(UnionFind z p) = finalRes where
  finalRes =
    if ILM.member i p
      then if ILM.member j p
        then go i j
        else (MergeResMissing j, u)
      else (MergeResMissing i, u)
  go ix1 jx1 =
    let (iacc, ix2) = ufFindRootAcc p [] ix1
        (acc, jx2) = ufFindRootAcc p iacc jx1
    in if ix2 == jx2
      then
        let res = MergeResUnchanged ix2
        in case acc of
          [] -> (res, u)
          _ -> let p' = foldr (`ILM.insert` ix2) p acc
              in (res, UnionFind z p')
      else
        let kx = ufOnConflict ix2 jx2
            kacc
              | ix2 < jx2 = if jx1 == jx2 then jx1:acc else jx2:jx1:acc
              | otherwise = if ix1 == ix2 then ix1:acc else ix2:ix1:acc
            p' = foldr (`ILM.insert` kx) p kacc
        in (MergeResChanged kx, UnionFind (z - 1) p')

-- | Merge two classes in the UF
ufMerge :: (Coercible x Int, Ord x) => x -> x -> State (UnionFind x) (MergeRes x)
ufMerge i j = state (ufMergeInc i j)

-- | The result of trying to merge multiple elements of the 'UnionFind'
data MergeManyRes x =
    MergeManyResEmpty
  | MergeManyResEmbed !(MergeRes x)
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic)
  deriving anyclass (NFData)

ufFindAllSeqInc :: (Coercible x Int, Eq x) => [x] -> UnionFind x -> (Either x (IntLikeSet x), UnionFind x)
ufFindAllSeqInc = go ILS.empty where
  go !acc !xs !u =
    case xs of
      [] -> (Right acc, u)
      y:ys ->
        let (mz, u') = ufFindInc y u
        in case mz of
          Nothing -> (Left y, u')
          Just z -> go (ILS.insert z acc) ys u'

ufMergeManyInc :: (Coercible x Int, Ord x) => IntLikeSet x -> UnionFind x -> (MergeManyRes x, UnionFind x)
ufMergeManyInc cs u =
  case ILS.toList cs of
    [] -> (MergeManyResEmpty, u)
    [h] -> (MergeManyResEmbed (MergeResUnchanged h), u)
    hs ->
      let (e, u') = ufFindAllSeqInc hs u
      in case e of
        Left x -> (MergeManyResEmbed (MergeResMissing x), u')
        Right xs ->
          case ILS.minView xs of
            Nothing -> error "impossible"
            Just (y, ys) ->
              if ILS.null ys && ILS.member y cs
                then (MergeManyResEmbed (MergeResUnchanged y), u')
                else
                  let UnionFind z p = u'
                      p' = foldr (`ILM.insert` y) p (ILS.toList ys)
                      u'' = UnionFind z p'
                  in (MergeManyResEmbed (MergeResChanged y), u'')

ufMergeMany :: (Coercible x Int, Ord x) => IntLikeSet x -> State (UnionFind x) (MergeManyRes x)
ufMergeMany = state . ufMergeManyInc
