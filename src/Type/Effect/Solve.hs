module Type.Effect.Solve where

import Type.Effect.Common as Common
import Type.Effect.Env as Env
import qualified Data.List as List

import qualified Data.UnionFind.IO as UF

import qualified Control.Monad as Monad
import qualified Data.Map as Map

import Control.Applicative

--import Data.IORef

import Debug.Trace (trace)


--type SetStore = (Map.Map Int PatInfo)
--type SetRef = IORef SetStore

joinAnn :: (AnnVar PatInfo) -> Maybe PatInfo -> IO ()
joinAnn v@(AnnVar (_, uf) ) info = do
  (i, oldInfo) <- UF.descriptor uf
  case (oldInfo, info) of
    (_, Nothing) -> return ()
    (Nothing, Just i) -> setAnn v i
    (Just inf1, Just inf2) -> UF.setDescriptor uf (i, Just $ joinPatInfo inf1 inf2)
  

solve :: PatMatchAnnotations -> AnnConstraint PatInfo -> IO (PatMatchAnnotations, [(PatInfo, PatInfo )])
solve env constr = do


  let orderedConsts = List.sortBy orderConstrs $ linearizeConstrs constr

  let processConstr c =
        case c of
          Unify t1 t2 -> do
            _ <- unifyConstrs t1 t2
            return []
          --InstanceOf t1 scheme -> do
          --  newTy <- instantiate env scheme
          --  unifyConstrs t1 newTy
          Contains (VarAnnot v) info -> do
            currentSet <- varAnn v
            joinAnn v (Just info) 
            return []
          Contains (BaseAnnot info1) info2 -> 
            error "TODO manual check if contained"
          OnlyContains _ _ -> return []
          GeneralizedContains _ _ -> return []


  warnings <- concat `fmap` Monad.forM orderedConsts processConstr

  let pairs = Map.toList env
  --We only normalize schemes that weren't imported
  newPairs <- Monad.forM pairs
             (\ (k,v) -> do
                     newV <- normalizeScheme v
                     return (k, newV)
                 )
  
  let retEnv = Map.fromList $ newPairs
  return (retEnv, warnings)

normalize :: PatAnn -> IO PatAnn
normalize (VarAnnot v) = do
      maybeInfo <- varAnn v 
      case maybeInfo of
        Just info -> BaseAnnot <$> normalizeInfo info
        Nothing -> return $ VarAnnot $ v
normalize (Union a1 a2) = Union <$> (normalize a1) <*> (normalize a2)
normalize Empty = return Empty
normalize (BaseAnnot info) = BaseAnnot <$> normalizeInfo info

normalizeScheme :: AnnotScheme PatInfo -> IO (AnnotScheme PatInfo)
normalizeScheme (SchemeAnnot ann) = SchemeAnnot <$> normalize ann
normalizeScheme  (AnnForAll vars _ ann) = do
  --Rewrite variables based on their annotations
  
  unifiedVars <-
        List.nub <$> Monad.mapM reprVar vars
  
  normalAnn <- normalize ann --TODO remove non-free vars?
  let usedVars = occurringVars normalAnn
  let newVars = case (usedVars List.\\ unifiedVars) of
        [] -> usedVars
        x -> usedVars -- error $ "Free varaibles " ++ show x ++ " never quantified during inference"
        
  return $ AnnForAll (newVars `List.intersect` usedVars) true normalAnn 
--TODO need to deal with constr? should have already incorporated it
--into descriptors for variables

normalizeInfo :: PatInfo -> IO PatInfo
normalizeInfo (PatLambda info1 info2) = PatLambda <$> normalize info1 <*> normalize info2
normalizeInfo (PatData s subs) = do
  subNormals <- Monad.forM subs (normalize)
  return $ PatData s subNormals
normalizeInfo (PatRecord fields rest) = do
  let (keys, vals) = unzip $ Map.toList fields
  subNormals <- Monad.forM vals (normalize)
  let newMap = Map.fromList $ zip (keys) subNormals
  newRest <- normalize rest
  return $ PatRecord newMap newRest
normalizeInfo Top  = return Top
normalizeInfo NativeAnnot = return  NativeAnnot
normalizeInfo (MultiPat fields) = do
  let (keys, vals) = unzip $ Map.toList fields
  subNormals <- Monad.forM vals (Monad.mapM $ normalize)
  let newMap = Map.fromList $ zip keys subNormals
  return $ MultiPat newMap

unifyInfo :: PatInfo -> PatInfo -> IO PatInfo
unifyInfo (PatLambda i1 i2) (PatLambda j1 j2) = do
  c1 <- unifyConstrs i1 j1
  c2 <- unifyConstrs i2 j2
  return  $ PatLambda c1 c2
unifyInfo (PatData s1 sub1) (PatData s2 sub2) = case (s1 == s2) of
  False -> error $ "Trying to unify with different ctors " ++ s1 ++ ", " ++ s2
  True -> do
    newSubs <- Monad.mapM (uncurry unifyConstrs) $ zip sub1 sub2
    return $ PatData s1 newSubs
unifyInfo r1@(PatRecord _ _) (PatRecord _ _ ) = return r1  --TODO implement this case
unifyInfo Top Top = return Top
unifyInfo NativeAnnot NativeAnnot = return NativeAnnot
unifyInfo i1@(MultiPat _) i2@(MultiPat _) = return $ joinPatInfo i1 i2 

--TODO: cases for Empty
unifyConstrs :: PatAnn -> PatAnn -> IO PatAnn
unifyConstrs (VarAnnot v1) (VarAnnot v2) = do
    --Read the sets stored at each variable
    --And merge them
    --TODO is this right? Shouldn't they be equal?
    m1 <- varAnn v1
    m2 <- varAnn v2
    newInfo <- case (m1, m2) of
          (Nothing, Nothing) -> return Nothing
          (Nothing, Just x) -> return $ Just x
          (Just x, Nothing) -> return $ Just x
          (Just x, Just y) -> do
            Just <$> unifyInfo x y
             
    unionVars v1 v2 newInfo
    VarAnnot <$> reprVar v1
unifyConstrs (VarAnnot v) (BaseAnnot info) = do
  maybeCurrent <- varAnn v
  newInfo <- case maybeCurrent of
    Nothing -> return $ info 
    Just (info2) -> unifyInfo info info2
  setAnn v newInfo
  return $ BaseAnnot newInfo
  
unifyConstrs x y@(VarAnnot _) = unifyConstrs y x
unifyConstrs (BaseAnnot info1) (BaseAnnot info2) =
  BaseAnnot <$> unifyInfo info1 info2
unifyConstrs x y = return x --TODO other cases?
--TODO empty cases? this is not right
--TODO use unify to verify equal?

{-
  case (info1, info2) of
  (PatLambda a1 b1, PatLambda a2 b2) -> do
    l1 <- unifyConstrs a1 a2
    l2 <- unifyConstrs b1 b2
    return $ l1 ++ l2
  --TODO assert same size subs?
  (PatData s1 subs1, PatData s2 subs2) -> case s1 == s2 of
    False -> error "Unify DATA with non-equal strings"
    _ -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry $  unifyConstrs )
  (PatRecord dict1 rest1, PatRecord dict2 rest2) -> do --TODO assert dicts have same keys
    let allFields = Map.keys dict1
    recErrs <- concat `fmap` Monad.forM allFields 
              (\k -> unifyConstrs (dict1 Map.! k) (dict2 Map.! k) )
    restErrs <- unifyConstrs rest1 rest2
    return $ recErrs ++ restErrs
  --(PatOther subs1, PatOther subs2 ) -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry unifyConstrs )
  (Top, Top) -> return []
  (NativeAnnot, NativeAnnot) -> return []
  --_ -> return [] --TODO why are we getting this case?
  x -> error $ "Bug in unification for exhaustiveness checking: unify " ++ (show x)
-}

joinPatInfo :: PatInfo -> PatInfo -> PatInfo
joinPatInfo (PatLambda a1 b1 ) (PatLambda a2 b2 ) = PatLambda (joinAnnots a1 a2) (joinAnnots b1 b2)
joinPatInfo (PatRecord fields1 rest1) (PatRecord fields2 rest2) = Top --TODO record case!
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
