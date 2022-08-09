-- | Three-way diffing for EGraphs.
-- - Given a basis and a new version, (reasonably) cheaply find out the change set
-- - Given two change sets, find out the common changes
-- - Apply changes to base graph
module Overeasy.EDiff where
import Data.Hashable
import Data.Coerce (Coercible,coerce)
import Overeasy.EGraph
import Overeasy.Assoc
import Overeasy.EquivFind
import IntLike.Set (IntLikeSet)
import IntLike.Map (IntLikeMap)
import qualified IntLike.Set as ILS
import qualified IntLike.Map as ILM
import Control.Monad (MonadPlus, forM_)
import Control.Monad.Trans.State.Strict (execStateT)
import GHC.Stack
import Data.Maybe (fromMaybe)

import qualified Data.HashMap.Strict as HM

data EDiff o f = EDiff {
  ediff_joins :: IntLikeMap EClassId (IntLikeSet EClassId),
  ediff_analysis :: IntLikeMap EClassId o,
  ediff_new_nodes :: HM.HashMap (f EClassId) (Maybe EClassId)
 }
deriving instance (Eq o, Eq (f EClassId)) => Eq (EDiff o f)
deriving instance (Show o, Show (f EClassId)) => Show (EDiff o f)

yankILM :: (Coercible o Int, HasCallStack)  => o -> IntLikeMap o a -> a
yankILM o m = fromMaybe (error $ "yank: no such key " <> show (coerce o :: Int)) (ILM.lookup (coerce o) m)

type Base = EGraph
type New = EGraph

class DeltaAnalysis d where
   -- | `deltaAnalysis l r` substracts l from  r. Returns Nothing when the neutral element is the result
   -- join (deltaAnalysis l r) l = join l r
   --  At least should return Nothing if l == r.
   --  Nicer would be a heyting algebra, but the analysis almost certainly isn't distributive
   deltaAnalysis :: d -> d -> Maybe d
   -- | Extract common knowledge from two delta analyses. Nothign if nothing is in common.
   -- join (intersectAnalysis l r) l == l
   -- join (intersectAnalysis l r) r == r
   intersectAnalysis :: d -> d -> Maybe d

threeWayDiff :: (DeltaAnalysis d, Hashable (f EClassId)) => Base d f -> New d f -> EDiff d f
threeWayDiff base new = EDiff (diffMerges base new) (diffAnalysis base new) (HM.map Just (diffNewNodes base new))


mergeDiffs :: (Traversable f, DeltaAnalysis d, Hashable (f EClassId)) => EDiff d f -> EDiff d f -> EDiff d f
mergeDiffs l r = EDiff joins analysis newNodes
  where
    joins = alignDiffs (ediff_joins l) (ediff_joins r)
    broadcastl = toBroadcastMap (ediff_joins l) joins
    broadcastr = toBroadcastMap (ediff_joins r) joins

    analysis = alignAnalysis broadcastl l broadcastr r
    newNodes = alignNewNodes joins l r

applyDiff :: (Hashable (f EClassId), Traversable f, EAnalysis d f, MonadPlus m) => Base d f -> EDiff d f -> m (New d f)
applyDiff base diff = flip execStateT base $ do
    forM_ (ILM.elems (ediff_joins diff)) egMergeMany 
    forM_ (HM.toList (ediff_new_nodes diff)) $ \(t,p) -> do
        (_, n) <- egAddFlatTerm t
        case p of
          Nothing -> pure ()
          Just o -> () <$ egMerge n o
    forM_  (ILM.toList (ediff_analysis diff)) $ \(k,v) -> egAddAnalysis k [v]

    egRebuild


type Broadcast = IntLikeMap EClassId (IntLikeSet EClassId)
-- | When intersecting merge sets, we have smaller merge sets.
-- This means roots of a set is mapped to multiple roots of the split sets
-- Create a mapping from old roots to new roots so we can broadcast other data to the new sets
toBroadcastMap :: IntLikeMap EClassId (IntLikeSet EClassId) -> IntLikeMap EClassId (IntLikeSet EClassId) -> Broadcast
toBroadcastMap fullJoins intersectedJoins = ILM.fromListWith (<>) $ do
    newRoot <- ILM.keys intersectedJoins
    let oldRoot = yankILM newRoot backMap
    return (oldRoot, ILS.singleton newRoot)
  where
    backMap = ILM.fromList [(y,x) | (x,ys) <- ILM.toList fullJoins, y <- ILS.toList ys]


broadcastMap :: IntLikeMap EClassId a -> Broadcast -> IntLikeMap EClassId a
broadcastMap oldMap broadcast = ILM.fromList $ do
    (oldRoot, value) <- ILM.toList oldMap
    newRoot <- ILS.toList (yankILM oldRoot broadcast)
    return (newRoot, value)

type JoinMap = IntLikeMap EClassId (IntLikeSet EClassId)
-- | This is maybe broken?
-- - If a term is added, and the children intersect to the same equivalenc class, it is added in the intersection
-- - If they are added to classes which are merged in the result, it lands in the correct class
-- but FIXME: we do not iterate this currently.
-- If both sides add 1+1, we only unify the 1's
-- could use Pending to do the necessary topo sort.
-- Main problem is that we could run into collisions if we keep the class ids alive.
alignNewNodes :: (Traversable f, Hashable (f EClassId)) => JoinMap -> EDiff d f -> EDiff d f -> HM.HashMap (f EClassId) (Maybe EClassId)
alignNewNodes joins l r  = HM.intersectionWith (\a b -> if a == b then a else Nothing) (toCanon l) (toCanon r)
  where
    toCanon ks
        = HM.fromList
        [ (k',  v >>= (`ILM.lookup` rootMap))
        | (k,v) <- HM.toList(ediff_new_nodes ks)
        -- filter out terms whose children aren't in both maps
        -- could generalize this so that we survive if an equivalent child is also new in the other half
        , Just k' <- [canonicalize k]
        ]
    canonicalize = traverse (\x -> ILM.lookup x rootMap)
    rootMap = ILM.fromList [(y,x) | (x,ys) <- ILM.toList joins, y <- ILS.toList ys]

alignAnalysis :: (DeltaAnalysis d) => Broadcast -> EDiff d f -> Broadcast -> EDiff d f -> IntLikeMap EClassId d
alignAnalysis broadcastl l broadcastr r = ILM.intersectionWithMaybe (const deltaAnalysis) bl br
  where
    bl = broadcastMap (ediff_analysis l) broadcastl
    br = broadcastMap (ediff_analysis r) broadcastr

alignDiffs :: IntLikeMap EClassId (IntLikeSet EClassId) -> IntLikeMap EClassId (IntLikeSet EClassId) -> IntLikeMap EClassId (IntLikeSet EClassId)
alignDiffs a b = go ILS.empty mempty [(k,v) | (k,vs) <-  ILM.toList a, v <- ILS.toList vs]
  where
    go _seen acc [] = acc
    go seen acc ((rx, x):xs) 
      | ILS.member x seen = go seen acc xs
      | Just bR <- ILM.lookup x toRootB
      = let common = ILS.intersection (yankILM rx a) (yankILM bR b)
        in go (ILS.union common seen) (ILM.insert x common acc) xs
      | otherwise = go seen acc xs

    toRootB :: IntLikeMap EClassId EClassId
    toRootB = ILM.fromList [(y,x) | (x,ys) <- ILM.toList b, y <- ILS.toList ys]


-- | Grab all analysis elements newer than base. This contains one entry per
-- canonical class, including classes newer than base
diffAnalysis :: DeltaAnalysis d => Base d f -> New d f -> IntLikeMap EClassId d
diffAnalysis base new = ILM.fromList $ do
    ks <- ILM.elems newerAnalysis
    k <- ILS.toList (toCanonSet (egEquivFind new) ks)
    let newAna = lookupNewAnalysis k
        oldAna = lookupOldAnalysis k
    Just diff <- [deltaAnalysis oldAna newAna]
    pure (k, diff)
  where
    oldEpoch = egEpoch base
    (_, newerAnalysis) = ILM.split (oldEpoch-1) (egAnaTimestamps new)
    lookupNewAnalysis cls = eciData $ yankILM cls (egClassMap new)
    lookupOldAnalysis cls = eciData $ yankILM cls (egClassMap base)

toCanonSet :: (Coercible a Int) => EquivFind a -> IntLikeSet a -> IntLikeSet a
toCanonSet ef eqs = ILS.map (\i -> efLookupRoot i ef) eqs

diffNewNodes :: Hashable (f EClassId) => Base d f -> New d f -> HM.HashMap (f EClassId) EClassId
diffNewNodes base new = out
  where
    newNodeIds = ILM.difference (egHashCons new) (egHashCons base)
    out  = HM.fromList [(lookupTerm nid, cid) | (nid, cid) <- ILM.toList newNodeIds]
    lookupTerm nid = assocPartialLookupByKey nid (egNodeAssoc new)

-- this only works when we haven't compacted since base, should we throw otherwise?
diffMerges :: Base d f -> New d f -> IntLikeMap EClassId (IntLikeSet EClassId)
diffMerges base new = deadByRoot
  where
    newlyDead = ILS.difference (egDeadClasses new) (egDeadClasses base)
    lookupRoot cls = efFindRoot cls (egEquivFind new)
    deadByRoot = ILM.mapWithKey (\k v -> ILS.insert k v) $ ILM.fromListWith (<>) $ do
      cls <- ILS.toList newlyDead
      Just root <- [lookupRoot cls]
      pure (root, ILS.singleton cls)
