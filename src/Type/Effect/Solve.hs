module Type.Effec.Solve where

import Type.Effect.Common as Common
import qualified Data.List as List

import qualified Data.UnionFind.IO as UF

import qualified Control.Monad as Monad
import qualified Data.Map as Map

solve :: AnnConstraint PatInfo -> IO [String]
solve constr = do
  let linearizeConstrs c = case c of
        ConstrAnd c1 c2 -> (linearizeConstrs c1) ++ (linearizeConstrs c2)
        AnnTrue -> []
        --Turn instances into unification when we can
        InstanceOf c1 (SchemeAnnot c2 ) -> [Unify c1 c2]
        _ -> [c]

  let orderedConsts = List.sortBy orderConstrs $ linearizeConstrs constr

  let processConstr c =
        case c of
          Unify t1 t2 -> unifyConstrs t1 t2
  
  concat `fmap` Monad.forM orderedConsts processConstr




unifyConstrs :: PatAnn -> PatAnn -> IO [String]
unifyConstrs (VarAnnot (AnnVar (_, uf1))) (VarAnnot (AnnVar (_, uf2))) = do
    UF.union uf1 uf2
    return []
unifyConstrs (VarAnnot (AnnVar (_, uf1))) (BaseAnnot info) = do
  storedDescr <- UF.descriptor uf1
  case storedDescr of
    PatUnInit -> do
      UF.setDescriptor uf1 info
      return []
    _ -> unifyConstrs (BaseAnnot storedDescr) (BaseAnnot info)
unifyConstrs x y@(VarAnnot _) = unifyConstrs y x
--TODO empty cases? this is not right
unifyConstrs (BaseAnnot info1) (BaseAnnot info2) = case (info1, info2) of
  (PatLambda a1 b1, PatLambda a2 b2) -> do
    l1 <- unifyConstrs a1 a2
    l2 <- unifyConstrs b1 b2
    return $ l1 ++ l2
  --TODO assert same size subs?
  (PatData s1 subs1, PatData s2 subs2) -> case s1 == s2 of
    False -> error "Unify DATA with non-equal strings"
    _ -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry unifyConstrs )
  (PatRecord dict1 rest1, PatRecord dict2 rest2) -> do --TODO assert dicts have same keys
    let allFields = Map.keys dict1
    recErrs <- concat `fmap` Monad.forM allFields 
              (\k -> unifyConstrs (dict1 Map.! k) (dict2 Map.! k) )
    restErrs <- unifyConstrs rest1 rest2
    return $ recErrs ++ restErrs
  (PatOther subs1, PatOther subs2 ) -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry unifyConstrs )
  (Top, Top) -> return []
  (NativeAnnot, NativeAnnot) -> return []
  _ -> error "Bug in unification for exhaustiveness checking"

