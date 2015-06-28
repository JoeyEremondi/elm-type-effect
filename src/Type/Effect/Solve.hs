module Type.Effec.Solve where

import Type.Effect.Common as Common
import qualified Data.List as List

import qualified Data.UnionFind.IO as UF

import qualified Control.Monad as Monad
import qualified Data.Map as Map

solve :: PatAnnEnv -> AnnConstraint PatInfo -> IO [String]
solve env constr = do
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
          --InstanceOf t1 scheme -> do
          --  newTy <- instantiate env scheme
          --  unifyConstrs t1 newTy
          Contains (VarAnnot (AnnVar (_, uf1))) info -> do
            currentInfo <- UF.descriptor uf1
            UF.setDescriptor uf1 $ joinPatInfo currentInfo info
            return []
          Contains (BaseAnnot info1) info2 -> 
            error "TODO manual check if contained"
  
  concat `fmap` Monad.forM orderedConsts processConstr


--TODO: cases for Empty
unifyConstrs :: PatAnn -> PatAnn -> IO [String]
unifyConstrs (VarAnnot (AnnVar (_, uf1))) (VarAnnot (AnnVar (_, uf2))) = do
    UF.union uf1 uf2
    return []
unifyConstrs (VarAnnot (AnnVar (_, uf1))) (BaseAnnot info) = do
  storedDescr <- UF.descriptor uf1
  case storedDescr of
    MultiPat dict -> case (Map.toList dict) of
        [] -> do
          UF.setDescriptor uf1 $ joinPatInfo storedDescr info
          return []
        _ -> error "Should not have Multi Dict at this point"
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
  --(PatOther subs1, PatOther subs2 ) -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry unifyConstrs )
  (Top, Top) -> return []
  (NativeAnnot, NativeAnnot) -> return []
  _ -> error "Bug in unification for exhaustiveness checking"


joinPatInfo :: PatInfo -> PatInfo -> PatInfo
joinPatInfo (PatLambda a1 b1 ) (PatLambda a2 b2 ) = PatLambda (joinAnnots a1 a2) (joinAnnots b1 b2)
joinPatInfo (PatRecord fields1 rest1) (PatRecord fields2 rest2) = error "TODO records"
joinPatInfo Top _ = Top
joinPatInfo _ Top = Top
joinPatInfo NativeAnnot _ = Top
joinPatInfo _ NativeAnnot = Top
joinPatInfo a@(PatData _ _) b@(MultiPat _) = joinPatInfo b a
joinPatInfo (MultiPat dict) (PatData str fields) =
  case Map.lookup str dict of
    Nothing -> MultiPat $ Map.insert str fields dict
    Just subFields ->
      MultiPat $ Map.insert str (zipWith joinAnnots fields subFields) dict
joinPatInfo (PatData str1 fields1) (PatData str2 fields2) =
  if (str1 == str2)
     then MultiPat $ Map.fromList [(str1 , zipWith joinAnnots fields1 fields2)]
  else MultiPat $ Map.fromList [(str1, fields1), (str2, fields2)]
joinPatInfo _ _ = error "Does not match underlying type system"

joinAnnots (BaseAnnot x) (BaseAnnot y) = BaseAnnot (joinPatInfo x y)
joinAnnots x y = Union x y
