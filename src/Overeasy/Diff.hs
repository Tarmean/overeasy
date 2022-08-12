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
  diff :: e -> e -> d
class Diff e d => DiffApply e d where
  applyDiff :: d -> e -> Maybe e
class Lattice d where
  lunion :: d -> d -> Maybe d
  lintersect :: d -> d -> Maybe d
  ltop :: d


newtype Merges a = Merges (EquivFind a)
    deriving (Eq, Show, Generic)

instance Coercible a Int => Lattice (Merges a) where
    lintersect (Merges efA) (Merges efB) = Just $ Merges $ efUnsafeNew $ go ILS.empty mempty [(k,v) | (k,vs) <-  ILM.toList a, v <- ILS.toList vs]
      where
        go _seen acc [] = acc
        go seen acc ((rx, x):xs) 
          | ILS.member x seen = go seen acc xs
          | Just bR <- ILM.lookup x toRootB
          = let common = ILS.intersection (yankILM rx a) (yankILM bR b)
            in go (ILS.union common seen) (ILM.insert x common acc) xs
          | otherwise = go seen acc xs
        a = efFwd efA
        b = efFwd efB
        toRootB = efBwd efB
    lunion (Merges a) (Merges b) = case runState (efMergeSets $ ILM.elems $ efFwd a) b of
        (Nothing, _) -> Nothing
        (Just _, o) -> Just (Merges o)
    ltop = Merges efNew
instance (Coercible a Int) => Diff (EquivFind a) (Merges a) where
    diff efA efB = Merges $ efNew -- efUnsafeNew out
      where
        removedRoots = ILM.difference (efFwd efA) (efFwd efB)
        out = ILM.fromListWith (<>) [(y, ILS.singleton x) | x <- ILM.keys removedRoots, let y = fromMaybe (error "Root not found") (efFindRoot x efB)]

data MapDiff k d = MapDiff {
  mapDiff :: !(IntLikeMap k d)
  } deriving (Eq, Show, Generic)
instance (Coercible k Int, Lattice d) => Lattice (MapDiff k d) where
    lunion (MapDiff a) (MapDiff b) = Just $ MapDiff $ ILM.unionWithMaybe (const lunion) a b
    lintersect (MapDiff da) (MapDiff db) = MapDiff <$> ILM.intersectionWithMaybeA step da db
      where
        step _ a b = fmap Just (lintersect a b)
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
  } deriving (Eq, Show, Generic)

instance (Lattice d) => Lattice (EDiff d) where
    lunion (EDiff la lb ) (EDiff ra rb) = case (lunion la ra , lunion lb rb) of
        (Just a, Just b) -> Just $ EDiff a b --(applyProduct a b)
        (Nothing, Just b) -> Just $ EDiff ltop b
        (Just a, Nothing) -> Just $ EDiff a ltop
        _ -> Nothing
    lintersect (EDiff la lb) (EDiff ra rb) = EDiff <$> lintersect la ra <*> lintersect lb rb
    ltop = EDiff ltop ltop


instance  (Diff d i, Lattice i, Eq i) => Diff (EGraph d f) (EDiff i) where
    diff base new = EDiff (diff (egEquivFind base) (egEquivFind new)) (MapDiff diffAnalysis)
      where
        diffAnalysis = ILM.fromList $ do
            let ks = mconcat (ILM.elems newerAnalysis)
            -- traceM ("diff ana" <> show ks)
            k <- ILS.toList  ks
            guard (ILM.member k (egClassMap base))
            let newAna = lookupNewAnalysis k
                oldAna = lookupOldAnalysis k
                diffOut = diff oldAna newAna
            -- traceM ("diff " <> show k <> " " <> show diffOut)
            guard $ diffOut /= ltop
            pure (k, diffOut)
        oldEpoch = egEpoch base
        (_, newerAnalysis) = ILM.split (oldEpoch-1) (egAnaTimestamps new)
        lookupNewAnalysis cls = eciData $ yankILM (canonNew cls) (egClassMap new)
        lookupOldAnalysis cls = eciData $ yankILM (canonOld cls) (egClassMap base)
        canonNew x = efLookupRoot x (egEquivFind new)
        canonOld x = efLookupRoot x (egEquivFind base)
instance (Eq i, EAnalysis d f, DiffApply d i) => DiffApply (EGraph d f) (EDiff i) where
    applyDiff (EDiff (Merges merges) (MapDiff analysis)) e = flip execStateT e $ do
        mapM_ egMergeMany (ILM.elems (efFwd merges))
        ef <- gets egEquivFind
        let
          normKey x = efLookupRoot x ef
          normed = ILM.fromList $ map (first normKey) $ ILM.toList analysis
        forM_ (ILM.toList normed) $ \(k,v) -> do
            old <- egGetAnalysis k
            let new = applyDiff v old
            case new of
              Nothing -> empty
              Just n -> egAddAnalysis k [n]

toCanonSet :: (Coercible a Int) => EquivFind a -> IntLikeSet a -> IntLikeSet a
toCanonSet ef eqs = ILS.map (\i -> efLookupRoot i ef) eqs



yankILM :: (Coercible o Int, HasCallStack)  => o -> IntLikeMap o a -> a
yankILM o m = fromMaybe (error $ "yank: no such key " <> show (coerce o :: Int)) (ILM.lookup (coerce o) m)
