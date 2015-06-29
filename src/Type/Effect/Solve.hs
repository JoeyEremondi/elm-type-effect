module Type.Effect.Solve where

import Type.Effect.Common as Common
import Type.Effect.Env as Env
import qualified Data.List as List

import qualified Data.UnionFind.IO as UF

import qualified Control.Monad as Monad
import qualified Data.Map as Map

import Control.Applicative

import Data.IORef

import Debug.Trace (trace)


type SetStore = (Map.Map Int PatInfo)
type SetRef = IORef SetStore

solve :: PatMatchAnnotations -> AnnConstraint PatInfo -> IO (PatMatchAnnotations, [(PatInfo, PatInfo )])
solve env constr = do
  varSets <- newIORef (Map.empty :: Map.Map Int PatInfo)


  let orderedConsts = List.sortBy orderConstrs $ linearizeConstrs constr

  let processConstr c =
        case c of
          Unify t1 t2 -> unifyConstrs varSets t1 t2
          --InstanceOf t1 scheme -> do
          --  newTy <- instantiate env scheme
          --  unifyConstrs t1 newTy
          Contains (VarAnnot (AnnVar (i, uf1))) info -> do
            intIndex <- if i < 0
                 then return (-1)
                 else UF.descriptor uf1
            currentSets <- readIORef varSets
            case (Map.lookup intIndex currentSets) of
              Nothing -> writeIORef varSets $ Map.insert intIndex
                        (joinPatInfo (MultiPat Map.empty ) info) currentSets
              (Just x) -> writeIORef varSets $ Map.insert intIndex (joinPatInfo x info) currentSets
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
                     newV <- normalizeScheme varSets v
                     return (k, newV)
                 )
  
  let retEnv = Map.fromList $ newPairs
  return (retEnv, warnings)

normalize :: SetRef -> PatAnn -> IO PatAnn
normalize ref (VarAnnot (AnnVar (i, uf1))) = do
      intIndex <- if i < 0
                 then return (-1)
                 else UF.descriptor uf1
      currentSets <- readIORef ref
      let maybeInfo = trace ("Normallize var " ++ show intIndex ++ " " ++ show currentSets ) $ Map.lookup intIndex currentSets
      case maybeInfo of
        Just info -> BaseAnnot <$> normalizeInfo ref info
        Nothing -> return $ VarAnnot $ AnnVar (intIndex, uf1)
normalize ref (Union a1 a2) = Union <$> (normalize ref a1) <*> (normalize ref a2)
normalize ref Empty = return Empty
normalize ref (BaseAnnot info) = BaseAnnot <$> normalizeInfo ref info

normalizeScheme :: SetRef -> AnnotScheme PatInfo -> IO (AnnotScheme PatInfo)
normalizeScheme ref (SchemeAnnot ann) = SchemeAnnot <$> normalize ref ann
normalizeScheme ref (AnnForAll vars _ ann) = do
  --Rewrite variables based on their annotations
  
  unifiedVars <-
        List.nub <$> Monad.forM vars
          (\ (AnnVar (i, uf) ) -> if i < 0
                                 then return $ AnnVar (i, uf)
                                 else do
                                   desc <- UF.descriptor uf
                                   return $ AnnVar (desc, uf) )
  
  let newVars = unifiedVars
  normalAnn <- normalize ref ann --TODO remove non-free vars?
  let usedVars = occurringVars normalAnn 
  return $ AnnForAll (newVars `List.intersect` usedVars) true normalAnn 
--TODO need to deal with constr? should have already incorporated it
--into descriptors for variables

normalizeInfo :: SetRef -> PatInfo -> IO PatInfo
normalizeInfo ref (PatLambda info1 info2) = PatLambda <$> normalize ref info1 <*> normalize ref info2
normalizeInfo ref (PatData s subs) = do
  subNormals <- Monad.forM subs (normalize ref)
  return $ PatData s subNormals
normalizeInfo ref (PatRecord fields rest) = do
  let (keys, vals) = unzip $ Map.toList fields
  subNormals <- Monad.forM vals (normalize ref)
  let newMap = Map.fromList $ zip (keys) subNormals
  newRest <- normalize ref rest
  return $ PatRecord newMap newRest
normalizeInfo ref Top  = return Top
normalizeInfo ref NativeAnnot = return  NativeAnnot
normalizeInfo ref (MultiPat fields) = do
  let (keys, vals) = unzip $ Map.toList fields
  subNormals <- Monad.forM vals (Monad.mapM $ normalize ref)
  let newMap = Map.fromList $ zip keys subNormals
  return $ MultiPat newMap

--TODO: cases for Empty
unifyConstrs :: SetRef -> PatAnn -> PatAnn -> IO [(PatInfo, PatInfo )]
unifyConstrs ref (VarAnnot (AnnVar (vi, uf1))) (VarAnnot (AnnVar (vj, uf2))) = do
    --Read the sets stored at each variable
    --And merge them
    --TODO is this right? Shouldn't they be equal?
    i <- if vi < 0
                 then return (-1)
                 else  UF.descriptor uf1
    j <-  if vj < 0
                 then return (-1)
                 else UF.descriptor uf2
    currentSets <- readIORef ref
    let m1 = Map.lookup i currentSets
    let m2 = Map.lookup j currentSets
    case (vi < 0, vj < 0) of
      (True, True) -> return []
      (True, False) -> return []
      (False, True) -> return []
      _ -> do
        k <- if vi < 0
                     then return (-1)
                     else  UF.descriptor uf1 --Different now that we've unioned
        let m3 = Map.lookup k currentSets
        let ijRemoved = Map.delete i $ Map.delete j currentSets
        let joinTwo mx my = case (mx, my) of
              (Nothing, Nothing) -> Nothing
              (Just x, Nothing) -> Just x
              (Just x, Just y) -> Just $ joinPatInfo x y
              (Nothing, Just y) -> Just y
        let join12 = joinTwo m1 m2
            join23 = joinTwo join12 m3
        case join23 of 
             Nothing -> return ()
             (Just x) -> writeIORef ref $ Map.insert k x ijRemoved
        return []
unifyConstrs ref (VarAnnot (AnnVar (i, uf1))) (BaseAnnot info) = do
  currentSets <- readIORef ref
  intIndex <- if i < 0
                 then return (-1)
                 else  UF.descriptor uf1
  let maybeCurrent = Map.lookup intIndex currentSets
  case maybeCurrent of
    Nothing -> writeIORef ref $ Map.insert intIndex info currentSets 
    Just (info2) -> writeIORef ref $ Map.insert intIndex (joinPatInfo info info2) currentSets
  return []
unifyConstrs ref x y@(VarAnnot _) = unifyConstrs ref y x
unifyConstrs _ _ _ = return []
--TODO empty cases? this is not right
--TODO use unify to verify equal?
unifyConstrs ref (BaseAnnot info1) (BaseAnnot info2) = case (info1, info2) of
  (PatLambda a1 b1, PatLambda a2 b2) -> do
    l1 <- unifyConstrs ref a1 a2
    l2 <- unifyConstrs ref b1 b2
    return $ l1 ++ l2
  --TODO assert same size subs?
  (PatData s1 subs1, PatData s2 subs2) -> case s1 == s2 of
    False -> error "Unify DATA with non-equal strings"
    _ -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry $  unifyConstrs ref )
  (PatRecord dict1 rest1, PatRecord dict2 rest2) -> do --TODO assert dicts have same keys
    let allFields = Map.keys dict1
    recErrs <- concat `fmap` Monad.forM allFields 
              (\k -> unifyConstrs ref (dict1 Map.! k) (dict2 Map.! k) )
    restErrs <- unifyConstrs ref rest1 rest2
    return $ recErrs ++ restErrs
  --(PatOther subs1, PatOther subs2 ) -> concat `fmap` Monad.forM (zip subs1 subs2) (uncurry unifyConstrs )
  (Top, Top) -> return []
  (NativeAnnot, NativeAnnot) -> return []
  --_ -> return [] --TODO why are we getting this case?
  x -> error $ "Bug in unification for exhaustiveness checking: unify " ++ (show x)


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
