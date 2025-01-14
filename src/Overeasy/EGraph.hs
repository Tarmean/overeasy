{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- -- | An E-Graph implementation
module Overeasy.EGraph
  ( EClassId (..)
  , ENodeId (..)
  , EAnalysis (..)
  , EAnalysisOff (..)
  -- , EAnalysisAlgebra (..)
  -- , EAnalysisFixpoint (..)
  , EAnalysisMerge(..)
  , EAnalysisIntersection(..)
  , EAnalysisHook (..)
  , EClassInfo (..)
  , EAnalysisChange(..)
  , EGraph
  , Epoch(..)
  , WorkItem
  , WorkList
  , egClassSource
  , egNodeSource
  , egEquivFind
  , egClassMap
  , egDeadClasses
  , egNodeAssoc
  , egHashCons
  , egWorkList
  , egClassSize
  , egNodeSize
  , egFindNode
  , egFindTerm
  , egClassInfo
  , egAnaWorklist
  , egNew
  , egClasses
  , egCanonicalize
  , egAddTerm
  , egAddFlatTerm
  , egAddAnalysis
  , egAddNodeSubId
  , egGetAnalysis
  , egMerge
  , egMergeMany
  , egUnionGraphs
  , egIntersectGraphs
  , egNeedsRebuild
  , egRebuild
  , egCanCompact
  , egCompact
  , egEpoch
  , egAnaTimestamps
  ) where

import GHC.Stack
import Debug.Trace (traceM)
import Control.DeepSeq (NFData)
import Control.Monad (unless, forM_, MonadPlus(mzero), when)
import Control.Monad.State.Strict (gets, modify', state, StateT(..), execStateT, evalStateT)
import Control.Monad.Writer (Writer, runWriter, tell, WriterT, execWriterT)
import Data.Foldable (foldl', toList)
import Data.Functor.Foldable (project)
import Data.Hashable (Hashable)
import Data.Kind (Type)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import IntLike.Map (IntLikeMap)
import qualified IntLike.Map as ILM
import IntLike.MultiMap (IntLikeMultiMap)
import qualified IntLike.MultiMap as ILMM
import IntLike.Set (IntLikeSet)
import qualified IntLike.Set as ILS
import Overeasy.Assoc (Assoc, AssocInsertRes (..), assocCanCompact, assocCompactInc, assocInsertInc, assocLookupByValue,
                       assocNew, assocPartialLookupByKey, assocToList, assocSize)
import Overeasy.Classes (Changed (..))
import Overeasy.EquivFind (EquivFind, EquivMergeSetsRes (..), efAddInc, efClosure, efCompactInc, efFindRoot,
                           efLookupLeaves, efLookupRoot, efMergeSetsInc, efNew, efRoots, efRootsSize)
import Overeasy.Recursion (RecursiveWhole, foldWholeM)
import Overeasy.Source (Source, sourceAddInc, sourceNew)
import Overeasy.StateUtil (stateFold)

import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Overeasy.Pending (Pending, pendingNew, pendingMarkKnown, pendingFinished)
import Control.Monad.Trans (lift)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Maybe (fromJust)
import Control.Monad.State (MonadState)

-- | An opaque class id
newtype EClassId = EClassId { unEClassId :: Int }
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Hashable, NFData)

-- | An opaque node id
newtype ENodeId = ENodeId { unENodeId :: Int }
  deriving stock (Show)
  deriving newtype (Eq, Ord, Enum, Hashable, NFData)

-- | The definition of an 'EGraph' analysis.
-- Should satisfy `eaJoin d [] == d`
-- TODO Allow these to signal additional information
-- so we can catch weird merges and so on
class EAnalysisMerge d => EAnalysis d f where
  eaMake :: f d -> d
  -- hook after class was updated
  eHook :: EAnalysisHook m d f => EClassId -> m ()
  eHook _ = pure ()
  -- hook after children of node changed
  -- used for propagators, alldifferent(a,b,c), a changes => propagatoe to b,c
  -- does NOT RUN if class changes, have to call for all children in eHook if thats wanted
  eHook1 :: EAnalysisHook m d f => EClassId -> f EClassId -> m ()
  eHook1 _ _ = pure ()
  alwaysHook :: proxy d f -> Bool
  alwaysHook _ = False
class EAnalysisMerge d where
  eaJoin :: d -> [d] -> d
  eaWhat :: d -> d -> EAnalysisChange
  default eaWhat :: Ord d => d -> d -> EAnalysisChange
  eaWhat l r 
    | l == r = UpdateNone
    | otherwise = UpdateBoth
  eaJoin2 :: d -> d -> (d, EAnalysisChange)
  eaJoin2 l r = (eaJoin l [r], eaWhat l r)

-- | Find information which holds accross both values
-- This is currently only used for egraph intersection
class EAnalysisIntersection d where 
   eaMeet :: d -> d -> d


class Monad m => EAnalysisHook m d f | m -> d f where
    eaClassData ::  EClassId -> m d
    eaAddTerm :: (EAnalysis d f, Functor f, Hashable (f EClassId)) => f EClassId -> m EClassId
    eaRefineAnalysis :: (EAnalysis d f)  => EClassId -> d -> m ()
    eaMerge :: EClassId -> EClassId -> m ()
    eaHalt :: m ()
    eaClassTerms :: (Hashable (f EClassId)) => EClassId -> m [f EClassId]
instance (MonadPlus m) => EAnalysisHook (StateT (EGraph d f) m) d f where
    eaClassData cid = do
      cmap <- gets egClassMap
      pure (eciData $ ILM.partialLookup cid cmap)
    eaClassTerms cid = do
      cmap <- gets egClassMap
      let nodes = (eciNodes $ ILM.partialLookup cid cmap)
      nodeTerms <- gets egNodeAssoc
      pure [assocPartialLookupByKey nid nodeTerms | nid <- ILS.toList nodes]
    eaAddTerm tid = do
       (_, trip) <- egAddNodeSubId tid
       pure (entClass trip)
    eaMerge cid cid2 = do
       m <- egMerge cid cid2
       case m of
         Just _ -> pure ()
         Nothing -> error "eaMerge: merge failed"
    eaRefineAnalysis tid d = do
       _ <- egAddAnalysis tid [d]
       pure ()
    eaHalt = mzero

    
 
egGetAnalysis :: MonadState (EGraph d f) m => EClassId -> m d
egGetAnalysis cid = do
  cmap <- gets egClassMap
  pure (eciData $ ILM.partialLookup cid cmap)



rightRequiresUpdate :: EAnalysisMerge d => d -> d -> Bool
rightRequiresUpdate l r = case eaWhat l r of
    UpdateRight -> True
    UpdateBoth -> True
    _ -> False
-- | Where does `eaJoin l r` land on the lattice?
-- We pretend we have some canonicalized partial order
data EAnalysisChange
    = UpdateRight -- ^ `l == eaJoin l r`
    | UpdateLeft -- ^ `r == eaJoin l r`
    | UpdateNone -- ^ `l == r`
    | UpdateBoth -- ^ `incomparable`

-- | A disabled analysis
data EAnalysisOff (f :: Type -> Type) = EAnalysisOff
  deriving (Eq, Ord, Show)

instance EAnalysis () f where
  eaMake _ = ()
instance EAnalysisMerge () where
  eaJoin _ _ = ()

-- newtype EAnalysisAlgebra d f = EAnalysisAlgebra
--   { unEAnalysisAlgebra :: f d -> d
--   }

-- TODO should also offer a monoid version that ignores the current data and recalculates
-- The monoid version is important for things like depth
-- instance (Semigroup d) => EAnalysis d f (EAnalysisAlgebra d f) where
--   eaMake (EAnalysisAlgebra g) fd = g fd
--   eaJoin _ d ds = sconcat (d :| ds)
--   eaWhat _ _ _ = UpdateNone

-- newtype EAnalysisFixpoint d f = EAnalysisFixpoint
--   { unEAnalysisFixpoint :: f d -> d
--   }

-- TODO should also offer a monoid version that ignores the current data and recalculates
-- The monoid version is important for things like depth
-- instance (Eq d, Semigroup d) => EAnalysis d f (EAnalysisFixpoint d f) where
--   eaMake (EAnalysisFixpoint g) fd = g fd
--   eaJoin _ d ds = sconcat (d :| ds)
--   eaWhat _ l r
--     | l == r = UpdateNone
--     | otherwise = UpdateBoth

data ENodeTriple d = ENodeTriple
  { entNode :: !ENodeId
  , entClass :: !EClassId
  , entData :: !d
  } deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

-- | Info stored for every class: analysis data and class members.
data EClassInfo d = EClassInfo
  { eciData :: !d
  , eciNodes :: !(IntLikeSet ENodeId)
  , eciParents :: !(IntLikeSet ENodeId)
  } deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

type WorkItem = IntLikeSet EClassId
type WorkList = Seq WorkItem
-- | When a class analysis is updated, we should rerun the parent nodes
type AnalysisWorklist = IntLikeSet ENodeId
newtype Epoch = Epoch Int
  deriving newtype (Eq, Ord, Hashable, Num, NFData)
  deriving stock (Show,Generic)

-- private ctor
data EGraph d f = EGraph
  { egClassSource :: !(Source EClassId)
  , egNodeSource :: !(Source ENodeId)
  , egEquivFind :: !(EquivFind EClassId)
  , egClassMap :: !(IntLikeMap EClassId (EClassInfo d))
  , egDeadClasses :: !(IntLikeSet EClassId)
  , egNodeAssoc :: !(Assoc ENodeId (f EClassId))
  , egHashCons :: !(IntLikeMap ENodeId EClassId)
  , egWorkList :: !WorkList
  , egAnaWorklist :: !AnalysisWorklist
  , egAnaTimestamps :: !(IntLikeMap Epoch  EClassId)
  , egEpoch :: Epoch
  } deriving stock (Generic)
egGetEpoch :: MonadState (EGraph d f) m => m Epoch
egGetEpoch = gets egEpoch

bumpAnalysisEpoch :: MonadState (EGraph d f) m => EClassId -> m ()
bumpAnalysisEpoch cid = do
  norm <- gets (efLookupRoot cid . egEquivFind)
  modify' $ \s -> s { egAnaTimestamps = ILM.insert (egEpoch s) cid (egAnaTimestamps s), egEpoch = egEpoch s + 1 }

deriving stock instance (Eq d, Eq (f EClassId)) => Eq (EGraph d f)
deriving stock instance (Show d, Show (f EClassId)) => Show (EGraph d f)
deriving anyclass instance (NFData d, NFData (f EClassId)) => NFData (EGraph d f)

-- | Number of equivalent classes in the 'EGraph' (see 'ufSize')
egClassSize :: EGraph d f -> Int
egClassSize = efRootsSize . egEquivFind

-- | Number of nodes in the 'EGraph'
egNodeSize :: EGraph d f -> Int
egNodeSize = ILM.size . egHashCons

-- | Lookup info for the given 'EClass'
egClassInfo :: EClassId -> EGraph d f -> Maybe (EClassInfo d)
egClassInfo c = ILM.lookup c . egClassMap

-- | Find the class of the given node, if it exists.
-- Note that you may have to canonicalize first to find it!
egFindNode :: (Hashable (f EClassId)) => f EClassId -> EGraph d f -> Maybe EClassId
egFindNode fc eg = do
  n <- assocLookupByValue fc (egNodeAssoc eg)
  ILM.lookup n (egHashCons eg)

-- | Find the class of the given term, if it exists
egFindTerm :: (RecursiveWhole t f, Traversable f, Hashable (f EClassId)) => t -> EGraph d f -> Maybe EClassId
egFindTerm t eg = foldWholeM (`egFindNode` eg) t

-- | Creates a new 'EGraph'
egNew :: EGraph d f
egNew = EGraph (sourceNew (EClassId 0)) (sourceNew (ENodeId 0)) efNew ILM.empty ILS.empty assocNew ILM.empty Empty ILS.empty ILM.empty 0

-- | Yields all root classes
egClasses :: MonadState (EGraph d f) m => m [EClassId]
egClasses = gets (efRoots . egEquivFind)

-- | Find the canonical form of a node
egCanonicalize :: (MonadState (EGraph d f) m, Traversable f) => f EClassId -> m (Maybe (f EClassId))
egCanonicalize fc = fmap (\ef -> traverse (`efFindRoot` ef) fc) (gets egEquivFind)

-- private
egCanonicalizeInternal :: (MonadState (EGraph d f) m, Traversable f, Hashable (f EClassId)) => ENodeId -> m (ENodeId, Maybe (IntLikeSet ENodeId))
egCanonicalizeInternal x = state $ \eg ->
  let ef = egEquivFind eg
      assoc = egNodeAssoc eg
      node = assocPartialLookupByKey x assoc
      fz = fmap (`efLookupRoot` ef) node
      ((y, res), assoc') = assocInsertInc x fz assoc
  in case res of
    AssocInsertResUnchanged -> ((y, Nothing), eg)
    AssocInsertResMerged toDelete ->
      ((y, Just toDelete), eg { egNodeAssoc = assoc' })
    _ -> ((y, Nothing), eg { egNodeAssoc = assoc' })

-- private
data AddNodeRes d = AddNodeRes !Changed !(Seq (ENodeTriple d))
  deriving stock (Eq, Show, Generic)
  deriving anyclass (NFData)

instance Semigroup (AddNodeRes d) where
  AddNodeRes c1 p1 <> AddNodeRes c2 p2 = AddNodeRes (c1 <> c2) (p1 <> p2)

instance Monoid (AddNodeRes d) where
  mempty = AddNodeRes ChangedNo Seq.empty
  mappend = (<>)

-- private
egAddNodeSub :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, Functor f, Hashable (f EClassId)) => f (ENodeTriple d) -> m (Changed, ENodeTriple d)
egAddNodeSub fcd = do
  let fc = fmap entClass fcd
  -- important: node should already be canonicalized!
  -- first lookup the node in the assoc to ensure uniqueness
  mayNodeId <- gets (assocLookupByValue fc . egNodeAssoc)
  case mayNodeId of
    Just n -> do
      x <- gets (ILM.partialLookup n . egHashCons)
      eci <- gets (ILM.partialLookup x . egClassMap)
      let d = eciData eci
      pure (ChangedNo, ENodeTriple n x d)
    Nothing -> postAddNodeHook (fmap entClass fcd) $ state $ \eg ->
      -- node does not exist; get new node and class ids
      let (n, nodeSource') = sourceAddInc (egNodeSource eg)
          (x, classSource') = sourceAddInc (egClassSource eg)
          -- add it to the uf (can discard return value since it's a new id, will be the same)
          (_, ef') = efAddInc x (egEquivFind eg)
          -- add it to the assoc (ignore and partial by construction)
          (_, assoc') = assocInsertInc n fc (egNodeAssoc eg)
          -- insert into the hashcons
          hc' = ILM.insert n x (egHashCons eg)
          -- analyze the node and put that info in the class map
          d = eaMake (fmap entData fcd)
          eci = EClassInfo d (ILS.singleton n) ILS.empty
          classMap' = ILM.insert x eci (egClassMap eg)
          eg' = eg { egNodeSource = nodeSource', egClassSource = classSource', egEquivFind = ef', egNodeAssoc = assoc', egHashCons = hc', egClassMap = classMap' }
      in ((ChangedYes, ENodeTriple n x d), eg')

postAddNodeHook :: forall f d m. (MonadState (EGraph d f) m, EAnalysisHook m d f, EAnalysis d f) => f EClassId -> m (Changed, ENodeTriple d) -> m (Changed, ENodeTriple d)
postAddNodeHook def m = do
     (c, nt) <- m
     if alwaysHook (undefined :: proxy d f) || c == ChangedYes 
       then do
         eHook (entClass nt)
         eHook1 (entClass nt) def
         bumpAnalysisEpoch (entClass nt)
         pure (c, nt)
       else pure (c, nt)

egAddNodeSubId :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, Functor f, Hashable (f EClassId)) =>  f EClassId -> m (Changed, ENodeTriple d)
egAddNodeSubId fc = do
  -- important: node should already be canonicalized!
  -- first lookup the node in the assoc to ensure uniqueness
  mayNodeId <- gets (assocLookupByValue fc . egNodeAssoc)
  case mayNodeId of
    Just n -> do
      x <- gets (ILM.partialLookup n . egHashCons)
      eci <- gets (ILM.partialLookup x . egClassMap)
      let d = eciData eci
      pure (ChangedNo, ENodeTriple n x d)
    Nothing -> postAddNodeHook fc $ state $ \eg ->
      -- node does not exist; get new node and class ids
      let (n, nodeSource') = sourceAddInc (egNodeSource eg)
          (x, classSource') = sourceAddInc (egClassSource eg)
          -- add it to the uf (can discard return value since it's a new id, will be the same)
          (_, ef') = efAddInc x (egEquivFind eg)
          -- add it to the assoc (ignore and partial by construction)
          (_, assoc') = assocInsertInc n fc (egNodeAssoc eg)
          -- insert into the hashcons
          hc' = ILM.insert n x (egHashCons eg)
          -- analyze the node and put that info in the class map
          getAnalysis c = eciData $ ILM.partialLookup c (egClassMap eg)
          fd = fmap getAnalysis fc
          d = eaMake fd
          -- TODO: post analysis hook
          eci = EClassInfo d (ILS.singleton n) ILS.empty
          classMap' = ILM.insert x eci (egClassMap eg)
          eg' = eg { egNodeSource = nodeSource', egClassSource = classSource', egEquivFind = ef', egNodeAssoc = assoc', egHashCons = hc', egClassMap = classMap' }
      in ((ChangedYes, ENodeTriple n x d), eg')

egAddFlatTerm :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, Traversable f, Hashable (f EClassId)) =>  f EClassId -> m (Changed, EClassId)
egAddFlatTerm f = do
    mf <- egCanonicalize f
    f <- case mf of
       Nothing -> error "egAddFlatTerm: Canonicalize failed"
       Just f' -> pure f'
    (change, trip) <- egAddNodeSubId f
    let n = entNode trip
    let children = F.toList f
    unless (null children) $
      modify' $ \eg ->
        -- Add node to class parents (unless it's a self parent)
        let cm' = foldl' (\cm c -> ILM.adjust (\v -> v { eciParents = ILS.insert n (eciParents v) }) c cm) (egClassMap eg) children
        in eg { egClassMap = cm' }
    pure (change, entClass trip)

-- private
-- Similar in structure to foldWholeTrackM
egAddTermSub :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, RecursiveWhole t f, Traversable f, Hashable (f EClassId)) =>t -> m (AddNodeRes d, ENodeTriple d)
egAddTermSub = go where
  go t = do
    -- unwrap to work with the functor layer
    let ft = project t
    -- add all child nodes
    frx <- traverse go ft
    -- collect info generated from child nodes and leave pure structure
    let (AddNodeRes changed1 children, fx) = sequenceA frx
    -- now fx should be canonicalized by construction
    -- add the node to get its node and class ids
    (changed2, z@(ENodeTriple n _ _)) <- egAddNodeSub fx
    -- now update all its children to add this as a parent
    unless (Seq.null children) $
      modify' $ \eg ->
        -- Add node to class parents (unless it's a self parent)
        let cm' = foldl' (\cm (ENodeTriple _ c _) -> ILM.adjust (\v -> if ILS.member n (eciNodes v) then v else v { eciParents = ILS.insert n (eciParents v) }) c cm) (egClassMap eg) children
        in eg { egClassMap = cm' }
    pure (AddNodeRes (changed1 <> changed2) (Seq.singleton z), z)

-- | Adds a term (recursively) to the graph. If already in the graph, returns 'ChangedNo' and existing class id. Otherwise
-- returns 'ChangedYes' and a new class id.
egAddTerm :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, RecursiveWhole t f, Traversable f, Hashable (f EClassId)) => t -> m (Changed, EClassId)
egAddTerm t = fmap (\(AddNodeRes c _, ENodeTriple _ x _) -> (c, x)) (egAddTermSub t)

-- | Merges two classes:
-- Returns 'Nothing' if the classes are not found
-- Otherwise returns the merged class id and whether anything has changed
-- If things have changed, then you must call 'egRebuild' before adding more terms.
-- (You can use 'egNeedsRebuild' to query this.)
egMerge :: MonadState (EGraph d f) m => EClassId -> EClassId -> m (Maybe Changed)
egMerge i j = egMergeMany (ILS.fromList [i, j])

egMergeMany :: MonadState (EGraph d f) m => IntLikeSet EClassId -> m (Maybe Changed)
egMergeMany cs = do
  mayRoots <- fmap (\ef -> traverse (`efFindRoot` ef) (ILS.toList cs)) (gets egEquivFind)
  case mayRoots of
    Nothing -> pure Nothing
    Just roots ->
      let rootsSet = ILS.fromList roots
      in if ILS.size rootsSet < 2
        then pure (Just ChangedNo)
        else do
          modify' (\eg -> eg { egWorkList = egWorkList eg :|> rootsSet })
          pure (Just ChangedYes)

-- | Have we merged classes and do we need to rebuild before adding more terms?
egNeedsRebuild :: EGraph d f -> Bool
egNeedsRebuild = not . null . egWorkList

-- private
-- Take the worklist (swapping for Empty).
egTakeWorklist :: MonadState (EGraph d f) m => m WorkList
egTakeWorklist = state $ \eg ->
  let wl = egWorkList eg
      eg' = case wl of { Empty -> eg; _ -> eg { egWorkList = Empty }}
  in (wl, eg')
-- private
-- Take the analysis worklist (swapping for Empty).
egTakeAnaWorklist :: MonadState (EGraph d f) m => m AnalysisWorklist
egTakeAnaWorklist = state $ \eg ->
  let wl = egAnaWorklist eg
      eg' = if ILS.null wl then eg else eg { egAnaWorklist = ILS.empty }
  in (wl, eg')


-- private
-- Folds over items in worklist to merge, returning:
-- 1. map of old class -> new class for changed classes only
-- 2. closure of remapped classes (includes roots)
egRebuildMerge :: MonadState (EGraph d f) m => WorkList -> m (IntLikeMap EClassId EClassId, IntLikeSet EClassId)
egRebuildMerge wl = finalRes where
  finalRes = state $ \eg ->
    let ef = egEquivFind eg
        dc = egDeadClasses eg
    in case efMergeSetsInc (toList wl) ef of
      EquivMergeSetsResChanged roots classRemapSet ef' ->
        let classRemap = ILM.fromList (fmap (\c -> (c, efLookupRoot c ef')) (ILS.toList classRemapSet))
            closure = ILS.difference (efClosure (ILS.toList roots) ef') dc
        in ((classRemap, closure), eg { egEquivFind = ef' })
      _ -> ((ILM.empty, ILS.empty), eg)

-- private
-- Loop through nodes of all changed classes and update the hashcons to point to new classes
egRebuildHashCons :: MonadState (EGraph d f) m => IntLikeMap EClassId EClassId -> m ()
egRebuildHashCons classRemap =
  modify' (\eg -> let hc' = foldl' (go (egClassMap eg)) (egHashCons eg) (ILM.toList classRemap) in eg { egHashCons = hc' }) where
  go cm hc (oldClassId, newClassId) =
    let eci = ILM.partialLookup oldClassId cm
        nodes = eciNodes eci
    in foldl' (flip (`ILM.insert` newClassId)) hc (ILS.toList nodes)

-- private
egRebuildAssoc :: (MonadState (EGraph d f) m, Traversable f, Hashable (f EClassId)) => IntLikeMap ENodeId EClassId -> IntLikeMap EClassId EClassId -> IntLikeSet EClassId -> m (IntLikeSet EClassId, WorkList)
egRebuildAssoc origHc classRemap touchedClasses = do
  hc <- gets egHashCons
  cm <- gets egClassMap
  -- For each class that we're going to merge
  stateFold (ILS.empty, Empty) (ILS.toList touchedClasses) $ \(ps, parentWl) c -> do
    -- Get the class info
    let eci = ILM.partialLookup c cm
    -- For each node in the class
    (finalChanged, finalParentWl) <- stateFold (False, parentWl) (ILS.toList (eciNodes eci)) $ \(changed', parentWl') n -> do
      -- Canonicalize it and add to the node map
      (newN, mayEquivNs) <- egCanonicalizeInternal n
      case mayEquivNs of
        Nothing -> pure (changed', parentWl')
        Just equivNs ->
          let allNs = ILS.insert newN equivNs
              allEquivClasses = ILS.map (`ILM.partialLookup` hc) allNs
          in if ILS.size allEquivClasses > 1
            then pure (True, parentWl' :|> allEquivClasses)
            else pure (changed', parentWl')
    -- Emit parents only class has changed or if any nodes have changed during canonicalization
    -- Note that we look up parents in the ORIGINAL hashcons because those are the ones that have the nodes pointing to this
    let emitParents = finalChanged || ILM.member c classRemap
        addlParents = ILS.map (`ILM.partialLookup` origHc) (eciParents eci)
        ps' = if emitParents then ILS.union addlParents ps else ps
    pure (ps', finalParentWl)

-- private
egRebuildCanonWl :: MonadState (EGraph d f) m => IntLikeMultiMap ENodeId ENodeId -> m WorkList
egRebuildCanonWl nodeMultiMap = goRoot where
  goRoot = do
    hc <- gets egHashCons
    -- For each node in the new -> old multimap
    pure (foldl' (goEach hc) Empty (ILMM.toList nodeMultiMap))
  goEach hc ms (_, oldNodes) =
    -- See what classes the nodes map to
    if ILS.size oldNodes > 1
      then
        -- Add to worklist if there are at least two classes for the same node
        let cs = ILS.map (`ILM.partialLookup` hc) oldNodes
        in if ILS.size cs > 1
          then ms :|> cs
          else ms
      else ms

-- private
egRebuildNodeRound :: (MonadState (EGraph d f) m, Traversable f, Hashable (f EClassId)) => IntLikeMap ENodeId EClassId -> WorkList -> IntLikeSet EClassId -> m (IntLikeSet EClassId, WorkList, IntLikeSet EClassId)
egRebuildNodeRound origHc wl parents = do
  -- First merge all classes together and get merged class sets
  (classRemap, classClosure) <- egRebuildMerge wl
  -- Now update the hashcons so node ids point to merged classes
  egRebuildHashCons classRemap
  -- Track all classes touched here
  let touchedClasses = ILS.union parents classClosure
  -- Traverse all classes and canonicalize their nodes,
  -- recording the mapping from old -> new
  -- Also track all possible parent classes
  -- TODO possible to rebuild node-by-node?
  (candParents, parentWl) <- egRebuildAssoc origHc classRemap touchedClasses
  -- Track parent classes for next round
  let finalParents = ILS.difference candParents touchedClasses
  pure (touchedClasses, parentWl, finalParents)

egRebuildClassSingle :: EAnalysisMerge d => IntLikeMap EClassId (EClassInfo d) -> EClassId -> IntLikeSet EClassId -> Writer (IntLikeSet ENodeId, IntLikeSet EClassId) (EClassInfo d)
egRebuildClassSingle baseCm newClass oldClasses =
  let EClassInfo rootData rootNodes rootParents = ILM.partialLookup newClass baseCm

      lookupNodes c = eciNodes (ILM.partialLookup c baseCm)
      lookupParents c = eciParents (ILM.partialLookup c baseCm)
      lookupData c = eciData (ILM.partialLookup c baseCm)

      (finalData, classToReanalyze) = egJoinAnalysis (newClass, rootData) [ (c, lookupData c) | c <-  ILS.toList oldClasses ]

      nodesToReanalyze = foldMap lookupParents (ILS.toList classToReanalyze)
      -- keep dead self nodes here. will be dropped in compact
      finalNodes = ILS.union rootNodes (foldMap lookupNodes (ILS.toList oldClasses))
      -- keep dead parent nodes here, just exclude self nodes. will be dropped in compact
      candParents = foldl' (\s c -> ILS.union s (lookupParents c)) rootParents (ILS.toList oldClasses)
      finalParents = ILS.difference candParents finalNodes
      finalInfo = EClassInfo finalData finalNodes finalParents
      shouldRerunHook = if not (ILS.null classToReanalyze) then ILS.singleton newClass else ILS.empty
  in tell (nodesToReanalyze, shouldRerunHook) *> pure finalInfo

-- private
-- Merge analyses for all classes together. When an old analyses
egJoinAnalysis :: (EAnalysisMerge d) => (EClassId, d) -> [(EClassId, d)] -> (d, IntLikeSet EClassId)
egJoinAnalysis parent oldData = (finalData, ILS.fromList dirtyClasses) where
    finalData = eaJoin (snd parent) (map snd oldData)
    dirtyClasses = [ cid | (cid, old) <- parent:oldData, rightRequiresUpdate finalData old ]


-- private
-- Rebuilds the classmap: merges old class infos into root class infos
-- Returns list of modified root classes
egRebuildClassMap :: (MonadState (EGraph d f) m, EAnalysis d f) => IntLikeSet EClassId -> m (IntLikeMultiMap EClassId EClassId, IntLikeSet EClassId)
egRebuildClassMap touchedClasses = state $ \eg ->
  let ef = egEquivFind eg
      dc = egDeadClasses eg
      roots = ILS.map (`efLookupRoot` ef) touchedClasses
      rootMap = ILM.fromList (fmap (\r -> (r, ILS.difference (efLookupLeaves r ef) dc)) (ILS.toList roots))

      -- FIXME! use rerunHookFor
      (newClassMap, (nodesToReanalyze, rerunHookFor)) = runWriter (ILM.traverseWithKey (egRebuildClassSingle (egClassMap eg)) rootMap)

      egAnaWorklist' = ILS.union (egAnaWorklist eg) nodesToReanalyze
      cm' = ILM.union newClassMap (egClassMap eg)
      dc' = foldl' ILS.union (egDeadClasses eg) (ILM.elems rootMap)
  in ((rootMap, rerunHookFor), eg { egClassMap = cm', egDeadClasses = dc', egAnaWorklist = egAnaWorklist' })

egAnalyzeTerm :: forall d f m. (MonadState (EGraph d f) m, Functor f, EAnalysis d f) => ENodeId -> m d
egAnalyzeTerm k = do
    classMap <- gets egClassMap
    let 
      lookupAnalysis :: EClassId -> d
      lookupAnalysis c = eciData (ILM.partialLookup c classMap)

    term <- gets (assocPartialLookupByKey k . egNodeAssoc)
    let anaTerm = fmap lookupAnalysis term
    pure (eaMake anaTerm)

egReanalyzeRounds :: (EAnalysisHook m d f, MonadState (EGraph d f) m, Functor f, EAnalysis d f) => m ()
egReanalyzeRounds = do
  wl <- egTakeAnaWorklist
  unless (ILS.null wl) $ do
    egReanalyzeRound wl
    egReanalyzeRounds

egGetNode :: MonadState (EGraph d f) m => ENodeId -> m (f EClassId)
egGetNode k = do
  assoc <- gets egNodeAssoc
  pure (assocPartialLookupByKey k assoc)
egReanalyzeRound :: (EAnalysisHook m d f, MonadState (EGraph d f) m, Functor f, EAnalysis d f) =>  AnalysisWorklist -> m ()
egReanalyzeRound wl = do
    origHc <- gets egHashCons
    let classReana = ILM.fromListWith ILS.union [ (ILM.partialLookup c origHc, ILS.singleton c) | c <- ILS.toList wl ]
    forM_ (ILM.toList classReana) $ \(clazz, reanaTerms) -> do
        o <- mapM (egAnalyzeTerm) (ILS.toList reanaTerms)
        egAddAnalysis clazz o
        mapM_ (\x -> eHook1 clazz =<< egGetNode x) (ILS.toList reanaTerms)
        bumpAnalysisEpoch clazz
egAddAnalysis :: forall d f m. (HasCallStack, EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f) => EClassId -> [d] -> m Bool
egAddAnalysis anaClass newData = do
    classMap <- gets egClassMap
    let 
      classData = ILM.partialLookup anaClass classMap
      oldData = eciData classData

      joined = eaJoin oldData newData
      isDirty = rightRequiresUpdate joined oldData
      addNewDirty wl = if isDirty then ILS.union (eciParents classData) wl else wl

      classData' = classData { eciData = joined }
    modify' (\eg -> eg { egClassMap = ILM.insert anaClass classData' (egClassMap eg), egAnaWorklist = addNewDirty (egAnaWorklist eg) })
    when (alwaysHook (undefined :: proxy d f) || isDirty) (eHook anaClass *> bumpAnalysisEpoch anaClass)
    pure isDirty

-- | Rebuilds the 'EGraph' after merging to allow adding more terms. (Always safe to call.)
egRebuild1 :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, Traversable f, Hashable (f EClassId)) => m (IntLikeMultiMap EClassId EClassId)
egRebuild1 = goRec where
  goRec = do
    -- Note the existing hashcons
    origHc <- gets egHashCons
    -- Read and clear the worklist - from now on nothing should add to it
    wl <- egTakeWorklist
    -- Merge and induce equivalences
    tc <- goNodeRounds origHc ILS.empty wl ILS.empty
    -- Now everything is merged so we only have to rewrite the changed parts of the classmap
    (out, rerunHooks) <- egRebuildClassMap tc
    mapM_ (\x -> eHook x *> bumpAnalysisEpoch x) (ILS.toList rerunHooks)
    egReanalyzeRounds
    pure out
  goNodeRounds !origHc !tc !wl !parents =
    if null wl && ILS.null parents
      then pure tc
      else do
        (newTc, newWl, newParents) <- egRebuildNodeRound origHc wl parents
        let mergedTc = ILS.union newTc tc
        goNodeRounds origHc mergedTc newWl newParents

-- | EAnalysis might dirty the graph, just throw a loop at it for now
egRebuild :: (EAnalysisHook m d f, MonadState (EGraph d f) m, EAnalysis d f, Traversable f, Hashable (f EClassId)) => m (IntLikeMultiMap EClassId EClassId)
egRebuild = loop mempty
  where
    loop acc = do
       o <- egRebuild1
       keepGoing <- gets egNeedsRebuild
       if keepGoing
       then loop (ILM.union o acc)
       else pure (ILM.union o acc)


egCanCompact :: EGraph d f -> Bool
egCanCompact eg = assocCanCompact (egNodeAssoc eg) || not (ILS.null (egDeadClasses eg))

-- Replace all parent nodes with the correct ones
egCompactParentClass :: IntLikeMap ENodeId ENodeId -> EClassInfo d -> EClassInfo d
egCompactParentClass nodeReplacements (EClassInfo dat nodes parents) =
  EClassInfo dat nodes (ILS.map (\n -> ILM.findWithDefault n n nodeReplacements) parents)

-- Remove dead self nodes
egCompactSelfClass :: IntLikeMap ENodeId ENodeId -> EClassInfo d -> EClassInfo d
egCompactSelfClass nodeReplacements (EClassInfo dat nodes parents) =
  EClassInfo dat (ILS.filter (not . (`ILM.member` nodeReplacements)) nodes) parents

findDeadNodeParentClasses :: Foldable f => Assoc ENodeId (f EClassId) -> [ENodeId] -> IntLikeSet EClassId
findDeadNodeParentClasses assoc = foldl' go ILS.empty where
  go s n = foldl' (flip ILS.insert) s (assocPartialLookupByKey n assoc)

-- Requires that class be rebuilt!
egCompactInc :: Foldable f => EGraph d f -> EGraph d f
egCompactInc eg =
  let ef = egEquivFind eg
      assoc = egNodeAssoc eg
      hc = egHashCons eg
      cm = egClassMap eg
      deadClasses = egDeadClasses eg
      -- remove dead nodes from assoc
      (nodeReplacements, assoc') = assocCompactInc assoc
      -- select all live classes that are parents of dead nodes
      deadNodeParentClasses = findDeadNodeParentClasses assoc (ILM.keys nodeReplacements)
      -- -- select all live classes that contain dead nodes
      deadNodeSelfClasses = ILS.fromList (fmap (`ILM.partialLookup` hc) (ILM.keys nodeReplacements))
      -- remove dead classes from hashcons
      hc' = foldl' (flip ILM.delete) hc (ILM.keys nodeReplacements)
      -- remove dead classes from unionfind
      (_, ef') = efCompactInc ef
      -- ef' = ef
      -- remove dead classes from classmap
      cm' = foldl' (flip ILM.delete) cm (ILS.toList deadClasses)
      -- rewrite dead parent nodes in classmap
      cm'' = foldl' (flip (ILM.adjust (egCompactParentClass nodeReplacements))) cm' (ILS.toList deadNodeParentClasses)
      -- -- rewrite dead self nodes in classmap
      cm''' = foldl' (flip (ILM.adjust (egCompactSelfClass nodeReplacements))) cm'' (ILS.toList deadNodeSelfClasses)
      egAnaTimestamps' = (egAnaTimestamps eg)
  in eg { egEquivFind = ef', egNodeAssoc = assoc', egClassMap = cm''', egHashCons = hc', egDeadClasses = ILS.empty, egAnaTimestamps = egAnaTimestamps' }

egCompact :: (MonadState (EGraph d f) m, Foldable f) => m ()
egCompact = modify' egCompactInc



type MUnion f d = StateT (EGraph d f) (StateT (IntLikeMap EClassId EClassId) Maybe)

-- | Merges two EGraphs. The resulting EGraph contains all nodes from both graphs.
-- When two nodes are in one equivalence class in either graph, they are merged in the resulting graph.
egUnionGraphs :: forall f d. (Hashable (f EClassId), EAnalysis d f, Traversable f) =>  EGraph d f -> EGraph d f -> Maybe (EGraph d f, IntLikeMap EClassId EClassId)
egUnionGraphs input1 input2 = runStateT (execStateT (processLoop (S.toList queue0) pending0) eg1) mempty
  where
    -- Uses the larger graph as base, insert the others node into it
    (eg1, eg2)
      | assocSize (egNodeAssoc input1) >= assocSize (egNodeAssoc input2) = (input1, input2)
      | otherwise = (input2, input1)
    depMap2 = M.fromList [(k, S.fromList (F.toList v)) | (k,v) <- assocToList (egNodeAssoc eg2)]
    (pending0, queue0) = pendingNew depMap2
    lookupClass2 :: ENodeId -> EClassId
    lookupClass2 n = ILM.partialLookup n (egHashCons eg2)
    lookupData2 :: EClassId -> d
    lookupData2 n = eciData (ILM.partialLookup n (egClassMap eg2))

    -- | Do merging in reverse topo order, starting with constants.
    processLoop :: [ENodeId] -> Pending EClassId ENodeId -> MUnion f d ()
    processLoop [] pending
       | pendingFinished pending = pure ()
       | otherwise = error "Processing not finished"
    processLoop nodes2 pending = do
       mapM_ go nodes2
       let classes = map lookupClass2 nodes2
           (pending', nodes2') =  pendingMarkKnown classes pending
       processLoop (S.toList nodes2') pending'

    go :: ENodeId -> MUnion f d ()
    go n2 = do
        let term = assocPartialLookupByKey n2 (egNodeAssoc eg2)
        term1 <- traverse getMapping term
        (_changed, cid1) <- egAddFlatTerm term1
        let class2 = lookupClass2 n2
        tryGetMapping class2 >>= \case
            Nothing -> do
               egAddAnalysis cid1 [lookupData2 class2]
               setMapping class2 cid1
            Just cid1' -> () <$ egMerge cid1 cid1'
    getMapping n = lift (gets (ILM.partialLookup n))
    tryGetMapping n = lift (gets (ILM.lookup n))
    setMapping n v = lift (modify' (ILM.insert n v))




type EClassLeft = EClassId
type EClassRight = EClassId
type EClassOut = EClassId
type MIntersect f d = StateT (EGraph d f) (StateT (IntLikeMap EClassLeft (IntLikeSet EClassOut), IntLikeMap EClassOut EClassRight, HashMap (EClassLeft, EClassRight) EClassOut) Maybe)

-- | Feels very similar to NFA intersection, but I wrote this while very tired so I based it on https://github.com/remysucre/eggegg/blob/main/src/main.rs
egIntersectGraphs  :: forall f d. (Show (f EClassId), EAnalysisIntersection d, Hashable (f EClassId), EAnalysis d f, Traversable f) => EGraph d f -> EGraph d f -> Maybe (EGraph d f)
egIntersectGraphs left0 right0 = evalStateT (execStateT (goConstructors *> goOuter)  egNew) (ILM.empty, ILM.empty, HM.empty)
   where
    goOuter = do
      traceM $ "goOuter start "
      ch <- execWriterT go
      traceM $ "goOuter: " <> show ch
      case ch of
        ChangedYes -> goOuter
        ChangedNo -> egCompact

    isConstant s = length s == 0
    constIds = ILS.fromList (fmap fst $ HM.elems constantsBoth)
    constants1 = HM.fromList [(fmap undefined cons, lookupClass1 nid1) | (nid1, cons) <- assocToList (egNodeAssoc left0), isConstant cons]
    constants2 = HM.fromList [(cons, lookupClass2 nid2) | (nid2, cons) <- assocToList (egNodeAssoc right0), isConstant cons]
    constantsBoth = HM.intersectionWith (,) constants1 constants2
    goConstructors :: MIntersect f d ()
    goConstructors = fmap (const ()) $ execWriterT $ do
       forM_ (HM.toList constantsBoth) $ \(term, (class1, class2)) -> do
                let termm = fmap undefined term
                (_, classMid) <- inEgg (egAddFlatTerm termm)
                insertMid class1 classMid
                setRight classMid class2
                tryInsertBack class1 class2 classMid

    go :: WriterT Changed (MIntersect f d) ()
    go = do
       forM_ (assocToList (egNodeAssoc left0)) $ \(node1,term1) -> do
          let class1 = lookupClass1 node1
          when (not $ ILS.member class1 constIds) $ do
              termms <- resolveTerm term1
              forM_ termms $ \termm -> do
                  mterm2 <- traverse lookupRight termm
                  case sequence mterm2 of
                    Nothing -> pure ()
                    Just term2 -> do
                        case lookupNode2 term2 of
                          Nothing -> pure ()
                          Just node2 -> do
                            let class2 = lookupClass2 node2
                            (isNew, classMid) <- inEgg (egAddFlatTerm termm)
                            traceM ("Add term " <> show term1 <> ", " <> show (class1, class2, isNew) <> ", " <> show classMid)
                            tell isNew
                            insertMid class1 classMid
                            setRight classMid class2
                            tryInsertBack class1 class2 classMid

    insertMid :: EClassLeft -> EClassOut -> WriterT Changed (MIntersect f d) ()
    insertMid class1 classMid = do
        lift $ lift $ modify' $ over1 $ flip ILM.alter class1 $ \case
            Nothing -> Just (ILS.singleton classMid)
            Just classes -> Just (ILS.insert classMid classes)
    tryInsertBack :: EClassLeft -> EClassRight -> EClassOut -> WriterT Changed (MIntersect f d) ()
    tryInsertBack class1 class2 classMid = do
        prev <- lift $ lift $ gets $ \(_,_,m) -> HM.lookup (class1,class2) m
        case prev of
          Just out -> do
            change <- fmap fromJust (inEgg (egMerge classMid out))
            _ <- inEgg egRebuild
            tell change
          Nothing -> do
              lift $ lift $ modify' $ over3 $ HM.insert (class1, class2) classMid
              let d1 = lookupData1 class1
                  d2 = lookupData2 class2
                  meet = eaMeet d1 d2
              inEgg (() <$ egAddAnalysis classMid [meet])
    setRight :: EClassOut -> EClassRight -> WriterT Changed (MIntersect f d) ()
    setRight classMid class2 = lift $ lift $ modify' $ over2 $ ILM.insert classMid class2
    over1 f (a,b,c) = (f a, b,c)
    over2 f (a,b,c) = (a,f b,c)
    over3 f (a,b,c) = (a,b,f c)
    inEgg = lift
    lookupMid :: EClassLeft -> WriterT Changed (MIntersect f d) [EClassOut]
    lookupMid cl = lift $ lift $ gets (ILS.toList . ILM.findWithDefault ILS.empty cl . fst3)
    resolveTerm :: f EClassOut -> WriterT Changed (MIntersect f d) [f EClassOut]
    resolveTerm term = do
        classes' <- traverse lookupMid term
        pure (sequence classes')
    lookupRight :: EClassOut -> WriterT Changed (MIntersect f d) (Maybe EClassRight)
    lookupRight cl = lift $ lift $ gets (ILM.lookup cl . snd3)
    snd3 (_,b,_) = b
    fst3 (a,_,_) = a

    lookupNode2 :: f EClassRight -> Maybe ENodeId
    lookupNode2 cl = assocLookupByValue cl (egNodeAssoc right0)

    lookupClass2 :: ENodeId -> EClassRight
    lookupClass2 cl = ILM.findWithDefault (error "lookupClass2") cl (egHashCons right0)

    lookupClass1 :: ENodeId -> EClassLeft
    lookupClass1 cl = ILM.findWithDefault (error "lookupClass1") cl (egHashCons left0)

    lookupData1 :: EClassId -> d
    lookupData1 cl = eciData $ ILM.partialLookup cl (egClassMap left0)

    lookupData2 :: EClassId -> d
    lookupData2 cl = eciData $ ILM.partialLookup cl (egClassMap right0)



---- k[ls] in (s,t)
---- if k[fst ls] in s
---- if k[snd ls] in t
---- (s1,t1) = (s2,t2)  if s1=s2, t1=t2
----
----
---- for (f, ls) in l
----     for argl in ls:
----         for (s,t) in g where s == argl:
