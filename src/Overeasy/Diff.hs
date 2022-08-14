{-# LANGUAGE UndecidableInstances #-}
module Overeasy.Diff where
import IntLike.Set (IntLikeSet)
import qualified IntLike.Set as ILS
import GHC.Generics (Generic)
import Overeasy.EquivFind
import qualified IntLike.Map as ILM
import IntLike.Map (IntLikeMap)
import Overeasy.EGraph (EClassId(..), EGraph(..), Epoch(..), eciData, egMergeMany, egAddAnalysis, egGetAnalysis, EAnalysis)
import Data.Coerce (Coercible, coerce)
import GHC.Stack (HasCallStack)
import Data.Maybe (fromMaybe)
import Control.Monad.Trans.State.Strict (runState, execStateT, gets)
import Control.Monad (forM_, guard)
import Control.Applicative (empty)
import Data.Bifunctor (first)



class Lattice d => Diff e d | e -> d where
  diff :: HasCallStack => e -> e -> d
class Diff e d => DiffApply e d where
  applyDiff :: d -> e -> Maybe e
class Lattice d where
  lintersect :: d -> d -> Maybe d
  lunion :: d -> d -> Maybe d
  ltop :: d


newtype Merges a = Merges { getMerges :: EquivFind a}
    deriving (Eq, Show, Generic, Ord)

instance Coercible a Int => Lattice (Merges a) where
    lunion (Merges efA) (Merges efB) = Just $ Merges $ efUnsafeNew $ go ILS.empty mempty [(k,v) | (k,vs) <-  ILM.toList a, v <- ILS.toList vs]
      where
        go _seen acc [] = acc
        go seen acc ((rx, x):xs) 
          | ILS.member x seen = go seen acc xs
          | Just bR <- efLookupRootAll x efB
          = let common = ILS.intersection (ILM.partialLookup rx a) (ILM.partialLookup bR b)
            in go (ILS.union common seen) (ILM.insert x common acc) xs
          | otherwise = go seen acc xs
        a = efFwd efA
        b = efFwd efB
    lintersect (Merges a) (Merges b) = case runState (efMergeSets $ ILM.elems $ efFwd a) b of
        (Nothing, _) -> Nothing
        (Just _, o) -> Just (Merges o)
    ltop = Merges efNew
instance (Coercible a Int) => Diff (EquivFind a) (Merges a) where
    diff efA efB = Merges $ efUnsafeNew out
      where
        removedRoots = ILM.difference (efFwd efA) (efFwd efB)
        out = ILM.fromListWith (<>) [(y, ILS.singleton x) | x <- ILM.keys removedRoots, let y = efFindRootAll x efB]

data MapDiff k d = MapDiff {
  mapDiff :: !(IntLikeMap k d)
  } deriving (Eq, Show, Generic, Ord)
instance (Coercible k Int, Lattice d) => Lattice (MapDiff k d) where
    lintersect (MapDiff a) (MapDiff b) = Just $ MapDiff $ ILM.intersectionWithMaybe (const lintersect) a b
    lunion (MapDiff da) (MapDiff db) = MapDiff <$> ILM.unionWithMaybeA step da db
      where
        step _ a b = fmap Just (lunion a b)
    ltop = MapDiff mempty

class SemiDirectProduct l r where
    applyProduct :: l -> r -> r
instance Coercible Int k => SemiDirectProduct (Merges k) (MapDiff k d) where
    applyProduct (Merges l) (MapDiff r) = MapDiff $ ILM.union  broadcast unAffected
      where
        unMerged = ILM.difference (efFwd l) r
        broadcast = ILM.fromList [(k,d) | k <- ILM.keys unMerged, Just d <- [ILM.lookup k r]]

        unAffected = ILM.difference r (efBwd l)


data EDiff d = EDiff {
    eMerges :: Merges EClassId,
    eAna :: MapDiff EClassId d
  } deriving (Eq, Show, Generic, Ord)

instance (Lattice d) => Lattice (EDiff d) where
    lintersect (EDiff la lb ) (EDiff ra rb) = case (lintersect la ra , lintersect lb rb) of
        (Just a, Just b) -> Just $ EDiff a b --(applyProduct a b)
        (Nothing, Just b) -> Just $ EDiff ltop b
        (Just a, Nothing) -> Just $ EDiff a ltop
        _ -> Nothing
    lunion (EDiff la lb) (EDiff ra rb) = EDiff <$> lunion la ra <*> lunion lb rb
    ltop = EDiff ltop ltop


instance  (Diff d i, Lattice i, Eq i) => Diff (EGraph d f) (EDiff i) where
    diff base new 
      -- | not $ ILS.null missingDirty = error ("missingDirty: " ++ show missingDirty ++ " maps: " ++ show smarty ++ " merged: " <> show deadClasses <> "\n\nold epoch" <>  show (egEpoch base) <> " new epoch " <> show (egEpoch new) <> " new timestamps" <> show (egAnaTimestamps new))
      | otherwise = EDiff merged (MapDiff diffAnalysis)
      where
        merged = diff (egEquivFind base) (egEquivFind new)
        -- missingDirty= ILS.difference (ILS.fromList (ILM.keys diffAnalysis)) smarty
            
        diffAnalysis = ILM.fromList $ do
            let ks = ILS.toList smarty
            -- traceM ("diff ana" <> show ks)
            k <-  ks
            -- k <- ILS.toList  ks
            guard (ILM.member k (egClassMap base))
            let oldAna = lookupOldAnalysis k
            let newAna = lookupNewAnalysis k
                diffOut = diff oldAna newAna
            -- traceM ("diff " <> show k <> " " <> show diffOut)
            guard $ diffOut /= ltop
            pure (k, diffOut)
        smarty = ILS.fromList (ILM.elems newerAnalysis) `ILS.union`  deadClasses
        deadClasses = mconcat (ILM.elems (efFwd (getMerges merged)))
        oldEpoch = egEpoch base
        (_, newerAnalysis) = ILM.split (oldEpoch) (egAnaTimestamps new)
        lookupNewAnalysis cls = eciData $ ILM.partialLookup (canonNew cls) (egClassMap new)
        lookupOldAnalysis cls = eciData $ ILM.partialLookup cls (egClassMap base)
        canonNew x = efFindRootAll x (egEquivFind new)
        -- canonOld x = efFindRootAll x (egEquivFind base)
instance (Eq i, EAnalysis d f, DiffApply d i) => DiffApply (EGraph d f) (EDiff i) where
    applyDiff (EDiff (Merges merges) (MapDiff analysis)) e = flip execStateT e $ do
        mapM_ egMergeMany (ILM.elems (efFwd merges))
        ef <- gets egEquivFind
        let
          normKey x = efFindRootAll x ef
          normed = ILM.fromList $ map (first normKey) $ ILM.toList analysis
        forM_ (ILM.toList normed) $ \(k,v) -> do
            old <- egGetAnalysis k
            let new = applyDiff v old
            case new of
              Nothing -> empty
              Just n -> egAddAnalysis k [n]

toCanonSet :: (Coercible a Int) => EquivFind a -> IntLikeSet a -> IntLikeSet a
toCanonSet ef eqs = ILS.map (\i -> efFindRootAll i ef) eqs



