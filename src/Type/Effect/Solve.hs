module Type.Effect.Solve where

import Type.Effect.Common as Common
import Type.Effect.Env as Env
import qualified Data.List as List

import qualified Data.UnionFind.IO as UF

import qualified Control.Monad as Monad
import qualified Data.Map as Map

import Control.Applicative

solve :: PatMatchAnnotations -> AnnConstraint PatInfo -> IO (PatMatchAnnotations, [(PatInfo, PatInfo )])
solve env constr = do
  let linearizeConstrs c = case c of
        ConstrAnd c1 c2 -> (linearizeConstrs c1) ++ (linearizeConstrs c2)
        AnnTrue -> []
        --Turn instances into unification when we can
        --InstanceOf c1 (SchemeAnnot c2 ) -> [Unify c1 c2]
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
          OnlyContains _ _ -> return []
          GeneralizedContains _ _ -> return []


  warnings <- concat `fmap` Monad.forM orderedConsts processConstr

  let (keys, vals) = unzip $ Map.toList env
  newVals <- Monad.forM vals normalizeScheme
  
  let retEnv = Map.fromList $ zip keys newVals
  return (retEnv, warnings)

normalize :: PatAnn -> IO PatAnn
normalize (VarAnnot (AnnVar (_, uf1))) = do
      desc <- UF.descriptor uf1
      BaseAnnot <$> normalizeInfo desc
normalize (Union a1 a2) = Union <$> (normalize a1) <*> (normalize a2)
normalize Empty = return Empty
normalize (BaseAnnot info) = BaseAnnot <$> normalizeInfo info

normalizeScheme :: AnnotScheme PatInfo -> IO (AnnotScheme PatInfo)
normalizeScheme (SchemeAnnot ann) = SchemeAnnot <$> normalize ann
normalizeScheme (AnnForAll vars _ ann) = (AnnForAll vars true) <$> normalize ann
--TODO need to deal with constr? should have already incorporated it
--into descriptors for variables

normalizeInfo :: PatInfo -> IO PatInfo
normalizeInfo (PatLambda info1 info2) = PatLambda <$> normalize info1 <*> normalize info2
normalizeInfo (PatData s subs) = do
  subNormals <- Monad.forM subs normalize
  return $ PatData s subNormals
normalizeInfo (PatRecord fields rest) = do
  let (keys, vals) = unzip $ Map.toList fields
  subNormals <- Monad.forM vals normalize
  let newMap = Map.fromList $ zip (keys) subNormals
  newRest <- normalize rest
  return $ PatRecord newMap newRest
normalizeInfo Top  = return Top
normalizeInfo NativeAnnot = return  NativeAnnot
normalizeInfo (MultiPat fields) = do
  let (keys, vals) = unzip $ Map.toList fields
  subNormals <- Monad.forM vals (Monad.mapM normalize)
  let newMap = Map.fromList $ zip keys subNormals
  return $ MultiPat newMap

--TODO: cases for Empty
unifyConstrs :: PatAnn -> PatAnn -> IO [(PatInfo, PatInfo )]
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
  _ -> return [] --TODO why are we getting this case?
  --x -> error $ "Bug in unification for exhaustiveness checking: unify " ++ (show x)


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
joinPatInfo (MultiPat d) info =
  if Map.null d
  then info
  else (error $ "Does not match underlying type system " ++ show (d, info) )
joinPatInfo i1 i2 = error $ "Does not match underlying type system " ++ show (i1, i2)
joinPatInfo info (MultiPat d) =
  if Map.null d
  then info
  else (error $ "Does not match underlying type system " ++ show (d, info) )
joinPatInfo i1 i2 = error $ "Does not match underlying type system " ++ show (i1, i2)
joinAnnots (BaseAnnot x) (BaseAnnot y) = BaseAnnot (joinPatInfo x y)
joinAnnots x y = Union x y
