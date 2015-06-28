{-
Joseph Eremondi
UU# 4229924
APA Project 2
April 17, 2015
-}

{-# LANGUAGE ScopedTypeVariables #-}
module Type.Effect.Common where --(mkAnnot, closedAnnot, directRecord, emptyRec) where

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
import qualified Type.Constrain.Literal as Literal

import qualified Data.List as List
import qualified Data.UnionFind.IO as UF

import qualified Type.PrettyPrint as TP
import qualified Type.State as TS

import Data.IORef

import Data.Ord (comparing)

import qualified Data.UnionFind.IO as UF

--Generic data type for type annotations
data Annot info =
  BaseAnnot info
  -- | Empty
  | VarAnnot (AnnVar info)


data AnnotScheme info = SchemeAnnot (Annot info) | AnnForAll [AnnVar info] (Annot info) 

data AnnEnv info =
  AnnEnv
  {ref :: (IORef Int),
   dict :: (Map.Map String (AnnotScheme info)),
   importedInfo :: Env.Environment}

--TODO union-find variables?
newtype AnnVar info = AnnVar (Int, UF.Point info)

instance Eq (AnnVar info) where
  (AnnVar (x,_)) == (AnnVar (y,_)) = x == y

instance Ord (AnnVar info) where
  (AnnVar (x,_)) < (AnnVar (y,_)) = x < y

data AnnConstraint info =
  Contains (Annot info) info
  | Unify (Annot info) (Annot info)
  | ConstrAnd (AnnConstraint info ) (AnnConstraint info)
  -- | InstanceOf (Annot info) (AnnotScheme info)
  | AnnTrue
  | OnlyContains (Annot info) (Annot info)

constrNum :: AnnConstraint info -> Int
constrNum (AnnTrue) = -1
constrNum (Unify _ _) = 0
--constrNum (InstanceOf _ _) = 1
constrNum (Contains _ _) = 2
constrNum (OnlyContains _ _ ) = 3

--Order for constraints, used in solving
orderConstrs :: AnnConstraint info -> AnnConstraint info -> Ordering
orderConstrs = comparing constrNum

--Initialize a pool of variables, returning a source of new variables
initialEnv :: Env.Environment -> IO (AnnEnv info )
initialEnv tyEnv = do
  nextVar <- newIORef (0 :: Int)
  return $ AnnEnv nextVar (Map.empty) tyEnv
  
newVar :: PatAnnEnv -> IO (AnnVar PatInfo)
newVar env = do
  ret <- readIORef $ ref env
  writeIORef (ref env) (ret + 1)
  point <- UF.fresh ( PatUnInit)
  return $ AnnVar (ret, point)

--existsWith :: AnnEnv info -> (Annot info -> IO (AnnConstraint info) ) -> IO (AnnConstraint info)
existsWith env f = do
  fresh <- newVar env
  f (VarAnnot fresh)

addAnnToEnv :: String -> (AnnotScheme info) -> AnnEnv info -> AnnEnv info
addAnnToEnv var ty env = env {dict = Map.insert var ty (dict env)} 

readEnv :: String -> AnnEnv info -> (AnnotScheme info)
readEnv var env = (dict env) Map.! var

constructor = Env.constructor . importedInfo

--TODO avoid code duplication with type fragments?
data AnnFragment info = AnnFragment
    { typeEnv :: AnnEnv info
    , vars :: [AnnVar info]
    , typeConstraint :: AnnConstraint info
    }

emptyFragment :: AnnEnv info -> AnnFragment info
emptyFragment env =
    AnnFragment (env { dict = Map.empty}) [] AnnTrue

joinFragment :: AnnFragment info -> AnnFragment info -> AnnFragment info
joinFragment f1 f2 =
    AnnFragment
      { typeEnv =
           let
             env1 = typeEnv f1
             env2 = typeEnv f2
           in env1 { dict = Map.union (dict env1) (dict env2)}

      , vars =
          vars f1 ++ vars f2

      , typeConstraint =
          typeConstraint f1 /\ typeConstraint f2
      }

joinFragments :: AnnEnv info -> [AnnFragment info] -> AnnFragment info
joinFragments env =
    List.foldl' (flip joinFragment) $ emptyFragment env

      

--Info specific to exhaustiveness-analysis
data PatInfo =
  PatLambda PatAnn PatAnn
  | PatData String [PatAnn]
  | PatRecord (Map.Map String PatAnn) PatAnn
  | PatOther [PatAnn] --TODO need this?
  | Top
  | NativeAnnot
  | PatUnInit
  | MultiPat (Map.Map String [PatAnn])

type PatAnn = Annot PatInfo

type PatAnnEnv = AnnEnv PatInfo

type PatFragment = AnnFragment PatInfo

emptyAnnot = BaseAnnot $ PatOther []

--import Debug.Trace (trace, traceStack)
trace _ x = x

--emptyRec = termN EmptyRecord1

--mkClosedRecord l = record (Map.fromList l) $ termN EmptyRecord1

--subExprType subAnns = mkClosedRecord $ zipWith (\(i::Int) t -> ("_sub" ++ show i, [t]) ) [1..] subAnns


--showField (nm, args) = nm ++ " : " ++ (show $ map (TP.pretty TP.App) args)

--TODO make tail recursive?
--mkAnnot :: [(String, [PatAnn] )] -> Annot PatInfo -> Annot PatInfo
--mkAnnot fields otherAnnot = case fields of
--  [] -> otherAnnot
--  ((ctor, info) :rest) -> (BaseAnnot $ PatData ctor info ) `AnnotUnion` (mkAnnot rest otherAnnot )
  

--closedAnnot x = mkAnnot x (Empty)

and = foldr ConstrAnd true
x /\ y = ConstrAnd x y
true = AnnTrue
t1 === t2 = (t1 `Unify` t2 )

--Instantiate a type variable
instantiate :: PatAnnEnv -> AnnotScheme PatInfo -> IO PatAnn
instantiate env (SchemeAnnot annot) = return annot
instantiate env (AnnForAll vars annot) = do
  newVars <- mapM (\_ -> newVar env ) vars
  return $ substVars (Map.fromList $ zip vars newVars) annot

substVars :: Map.Map (AnnVar PatInfo) (AnnVar PatInfo ) -> PatAnn -> PatAnn
substVars subMap (VarAnnot v) = case Map.lookup v subMap of
  Nothing -> VarAnnot v
  (Just v2) -> VarAnnot v2
substVars subMap (BaseAnnot info) =
  let self = substVars subMap
  in BaseAnnot $ case info of
  (PatLambda x1 x2) -> PatLambda (self x1) (self x2)
  (PatData x1 x2) -> PatData x1 $ map self x2
  (PatRecord x1 x2) -> PatRecord (Map.map self x1) (self x2)
  (PatOther x) -> PatOther $ map self x
  Top -> Top
  NativeAnnot -> NativeAnnot
  PatUnInit -> PatUnInit
  (MultiPat x) -> MultiPat $ Map.map (map self) x


{-

directRecord :: [(String, Type )] -> Type -> Type
directRecord fields restOfRecord = trace ("Direct record " ++ show (map (\(f,x) -> showField (f,[x])) fields )  ) $
  let
    recDict = Map.fromList $ map (\(nm,argTy) -> (nm, [argTy]) ) fields
  in record recDict restOfRecord

-}
