module Type.Effect.Env where

import Type.Effect.Common

import Control.Arrow (second)
import Control.Applicative ((<$>))
import qualified Control.Monad as Monad
import Control.Monad.Error
import qualified Data.Map as Map
import qualified Text.PrettyPrint as PP

import qualified Reporting.Annotation as A
import qualified AST.Pattern as P
import qualified AST.Variable as V
import Reporting.PrettyPrint (pretty)
--import Type.Type
--import Type.Fragment
import Type.Environment as Env
--import qualified Type.Constrain.Literal as Literal

import qualified Data.List as List
import qualified Data.UnionFind.IO as UF

import qualified Type.PrettyPrint as TP
import qualified Type.State as TS

import Data.IORef

import Data.Ord (comparing)

import qualified Data.UnionFind.IO as UF

import Control.Applicative

import GHC.Stack

import AST.Type as AT

data AnnEnv info =
  AnnEnv
  {ref :: (IORef Int),
   dict :: (Map.Map String (AnnotScheme info)),
   importedInfo :: Env.Environment}




--Initialize a pool of variables, returning a source of new variables
initialEnv :: Env.Environment -> IO (AnnEnv info )
initialEnv tyEnv = do
  nextVar <- newIORef (0 :: Int)
  return $ AnnEnv nextVar (Map.empty) tyEnv
  
newVar :: PatAnnEnv -> IO (AnnVar PatInfo)
newVar env = do
  ret <- readIORef $ ref env
  writeIORef (ref env) (ret + 1)
  point <- UF.fresh ( patUnInit)
  return $ AnnVar (ret, point)




addAnnToEnv :: String -> (AnnotScheme info) -> AnnEnv info -> AnnEnv info
addAnnToEnv var ty env = env {dict = Map.insert var ty (dict env)} 

readEnv :: String -> AnnEnv info -> (AnnotScheme info)
readEnv var env = case Map.lookup var (dict env) of
  Nothing ->
    let
      unQual = (last $ words $ map (\c -> if c == '.' then ' ' else c ) var )
    in
     case (Map.lookup unQual (dict env)) of
       Nothing -> errorWithStackTrace $ "Variable " ++ var ++ " not in env " ++ (show $ Map.keys $ dict env )
       Just x -> x
  Just x -> x

constructor = Env.constructor . importedInfo

--TODO avoid code duplication with type fragments?
data AnnFragment info = AnnFragment
    { typeEnv :: (Map.Map String (Annot info))
    , vars :: [AnnVar info]
    , typeConstraint :: AnnConstraint info
    }

emptyFragment :: AnnFragment info
emptyFragment =
    AnnFragment Map.empty [] AnnTrue

joinFragment :: AnnFragment info -> AnnFragment info -> AnnFragment info
joinFragment f1 f2 =
    AnnFragment
      { typeEnv =
           let
             env1 = typeEnv f1
             env2 = typeEnv f2
           in Map.union env1 env2

      , vars =
          vars f1 ++ vars f2

      , typeConstraint =
          typeConstraint f1 /\ typeConstraint f2
      }

joinFragments :: [AnnFragment info] -> AnnFragment info
joinFragments =
    List.foldl' (flip joinFragment) $ emptyFragment





type PatAnnEnv = AnnEnv PatInfo


type PatFragment = AnnFragment PatInfo

--"Temporary:" add the variables of a fragment to a type-env
--This lets us generate constraints for recursive definitions
tempAddFrag :: PatAnnEnv -> PatFragment -> PatAnnEnv
tempAddFrag env frag = env {dict = Map.union (dict env) (Map.map SchemeAnnot $ typeEnv frag)}

addFragToEnv :: PatAnnEnv -> PatFragment -> AnnConstraint PatInfo -> PatAnnEnv
addFragToEnv env frag defConstr =
  let
    fragEnv = typeEnv frag
    schemeConstr = defConstr /\ (typeConstraint frag )
    closedEnv = Map.map ((closeScheme env schemeConstr) . SchemeAnnot ) fragEnv
  in env {dict = Map.union (dict env) closedEnv}  

closeScheme env con s@(AnnForAll _ _ _) = s
closeScheme env con (SchemeAnnot ann) =
  let
    varsToOmit = concatMap freeInScheme $ Map.elems (dict env)
    vars = List.nub $ (freeIn varsToOmit ann) ++ (freeInConstr varsToOmit con )
  in AnnForAll vars con ann



--Instantiate a type variable
instantiate :: PatAnnEnv -> AnnotScheme PatInfo -> IO (PatAnn, AnnConstraint PatInfo)
instantiate env (SchemeAnnot annot) = return (annot, true)
instantiate env (AnnForAll vars constrs annot) = do
  newVars <- mapM (\_ -> newVar env) vars
  let foldFun1 ann (oldVar , newVar ) = substVars oldVar newVar ann
  let foldFun2 c (oldVar , newVar ) = substConstraint oldVar newVar c
  newAnnot <- foldM foldFun1 annot $ zip vars newVars
  newConstr <- foldM foldFun2 constrs $ zip vars newVars
  return (newAnnot, newConstr)
 
  
--substScheme v1 v2 (SchemeAnnot info ) = SchemeAnnot <$> substVars v1 v2 info
--substScheme v1 v2 (AnnForAll _ scheme) = substScheme v1 v2 scheme

substConstraint :: (AnnVar PatInfo) -> (AnnVar PatInfo ) -> AnnConstraint PatInfo -> IO (AnnConstraint PatInfo)
substConstraint oldVar newVar constr =
  let
    sv = substVars oldVar newVar
    self = substConstraint oldVar newVar
  in case constr of
    (Contains x1 x2) -> do
      sub1 <- sv x1
      (BaseAnnot sub2) <- sv $ BaseAnnot x2
      return $ Contains sub1 sub2
    (Unify x1 x2) -> Unify <$> sv x1 <*> sv x2
    (ConstrAnd x1 x2) -> ConstrAnd <$> self x1 <*> self x2 
    AnnTrue -> return AnnTrue
    (OnlyContains x1 x2) -> OnlyContains <$> sv x1 <*> sv x2
    (GeneralizedContains x1 x2) -> GeneralizedContains <$> sv x1 <*> sv x2

substVars :: (AnnVar PatInfo) -> (AnnVar PatInfo ) -> PatAnn -> IO PatAnn
substVars vCurrent vsub (VarAnnot v) = do
  areSame <- return $ vCurrent == v --UF.equivalent (getUF vCurrent) (getUF v) 
  case areSame of
    False -> return $ VarAnnot v
    True -> return $ VarAnnot vsub
substVars vCurrent vsub (BaseAnnot info) = do
  let self = substVars vCurrent vsub
  newInfo <- case info of
    (PatLambda x1 x2) -> PatLambda <$> (self x1) <*> (self x2)
    (PatData x1 x2) -> (PatData x1) <$> mapM self x2
    (PatRecord x1 x2) -> do
      let pairs = Map.toList x1
      newPairs <- (zip (map fst pairs) ) <$> mapM self (map snd pairs )
      newX2 <- self x2
      return $ PatRecord (Map.fromList newPairs) newX2
    --(PatOther x) -> PatOther <$> mapM self x
    Top -> return Top
    NativeAnnot -> return NativeAnnot
    (MultiPat x) -> do
      let pairs = Map.toList x
      let fixPair (k, v) = do
            newV <- mapM self v
            return (k, newV)
      newPairs <- mapM fixPair pairs
      return $ MultiPat $ Map.fromList newPairs
  return $ BaseAnnot newInfo
substVars _ _ Empty = return Empty
substVars v1 v2 (Union i1 i2) = Union <$> substVars v1 v2 i1 <*> substVars v1 v2 i2

freeInScheme :: AnnotScheme PatInfo -> [AnnVar PatInfo]
freeInScheme (SchemeAnnot ann) = freeIn [] ann
freeInScheme (AnnForAll vars constr annot) = freeIn vars annot ++ freeInConstr vars constr

freeInConstr :: [AnnVar PatInfo] -> AnnConstraint PatInfo -> [AnnVar PatInfo]
freeInConstr bound c =
  let
    f = freeIn bound
  in case c of
    (Contains c1 c2) -> (f c1) ++ (f $ BaseAnnot c2)
    (Unify c1 c2) -> (f c1) ++ (f c2)
    (ConstrAnd c1 c2) -> (freeInConstr bound c1) ++ (freeInConstr bound c2)  
    AnnTrue -> []
    (OnlyContains c1 c2) -> (f c1) ++ (f c2)
    (GeneralizedContains c1 c2) -> (f c1) ++ (f c2)

freeIn :: [AnnVar PatInfo] -> PatAnn  -> [AnnVar PatInfo]
freeIn bound (VarAnnot v) =
  if v `elem` bound
  then []
  else [v]
freeIn bound Empty = []
freeIn bound (Union a1 a2) = (freeIn bound a1) ++ (freeIn bound a2)
freeIn bound (BaseAnnot info)  =
  let
    self = freeIn bound
  in case info of
    (PatLambda x1 x2) -> (self x1) ++ (self x2)
    (PatData _ x2) ->  (concatMap self x2)
    (PatRecord x1 x2) ->  (concatMap self $ Map.elems x1) ++ (self x2)
    --(PatOther x) ->  concatMap freeVars x
    Top -> []
    NativeAnnot -> []
    --PatUnInit -> []
    (MultiPat x) ->  concatMap self $ concat $ Map.elems x 


occurringVars :: PatAnn -> [AnnVar PatInfo]
occurringVars (VarAnnot v) = [v] 
occurringVars (BaseAnnot info) =
  case info of
    (PatLambda x1 x2) -> (occurringVars x1) ++ (occurringVars x2)
    (PatData _ x2) ->  (concatMap occurringVars x2)
    (PatRecord x1 x2) ->  (concatMap occurringVars $ Map.elems x1) ++ (occurringVars x2)
    --(PatOther x) ->  concatMap freeVars x
    Top -> []
    NativeAnnot -> []
    --PatUnInit -> []
    (MultiPat x) ->  concatMap occurringVars $ concat $ Map.elems x

--existsWith :: AnnEnv info -> (Annot info -> IO (AnnConstraint info) ) -> IO (AnnConstraint info)
existsWith env f = do
  fresh <- newVar env
  f (VarAnnot fresh)



