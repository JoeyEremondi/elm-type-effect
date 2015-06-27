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

--Generic data type for type annotations
data Annot info =
  BaseAnnot info
  | AnnotUnion (Annot info) (Annot info)
  | Empty
  | VarAnnot AnnVar

data AnnotScheme info = SchemeAnnot (Annot info) | AnnForAll AnnVar (AnnotScheme info) 

data AnnEnv info = AnnEnv (IORef Int) (Map.Map V.Canonical (AnnotScheme info))

--TODO union-find variables?
newtype AnnVar = AnnVar Int

data AnnConstraint info =
  Contains (Annot info) (Annot info)
  | ConstrAnd (AnnConstraint info ) (AnnConstraint info)
  | AnnTrue

--Initialize a pool of variables, returning a source of new variables
initialEnv :: IO (AnnEnv info )
initialEnv = do
  nextVar <- newIORef (0 :: Int)
  return $ AnnEnv nextVar (Map.empty)
  
newVar :: AnnEnv info -> IO AnnVar
newVar (AnnEnv ref _) = do
  ret <- readIORef ref
  writeIORef ref (ret + 1)
  return $ AnnVar ret

existsWith :: AnnEnv info -> (Annot info -> IO (AnnConstraint info) ) -> IO (AnnConstraint info)
existsWith env f = do
  fresh <- newVar env
  f (VarAnnot fresh)

addAnnToEnv :: V.Canonical -> (AnnotScheme info) -> AnnEnv info -> AnnEnv info
addAnnToEnv var ty (AnnEnv ref dict ) = AnnEnv ref $ Map.insert var ty dict 

readEnv :: V.Canonical -> AnnEnv info -> (AnnotScheme info)
readEnv var (AnnEnv _ dict) = dict Map.! var

--TODO avoid code duplication with type fragments?
data AnnFragment info = AnnFragment
    { typeEnv :: AnnEnv info
    , vars :: [AnnVar]
    , typeConstraint :: AnnConstraint info
    }

emptyFragment :: AnnEnv info -> AnnFragment info
emptyFragment (AnnEnv ref _) =
    AnnFragment (AnnEnv ref Map.empty) [] AnnTrue

joinFragment :: AnnFragment info -> AnnFragment info -> AnnFragment info
joinFragment f1 f2 =
    AnnFragment
      { typeEnv =
           let
             (AnnEnv ref dict1 ) = typeEnv f1
             (AnnEnv _ dict2) = typeEnv f2
           in AnnEnv ref $ Map.union dict1 dict2

      , vars =
          vars f1 ++ vars f2

      , typeConstraint =
          typeConstraint f1 /\ typeConstraint f2
      }
    

--Info specific to exhaustiveness-analysis
data PatInfo =
  PatLambda PatAnn PatAnn
  | PatData String [PatAnn]
  | PatOther [PatAnn] --Catch-all case for tuples, records, etc.
  | Top
  | NativeAnnot

type PatAnn = Annot PatInfo

type PatAnnEnv = AnnEnv PatInfo

type PatFragment = AnnFragment PatInfo



--import Debug.Trace (trace, traceStack)
trace _ x = x

--emptyRec = termN EmptyRecord1

--mkClosedRecord l = record (Map.fromList l) $ termN EmptyRecord1

--subExprType subAnns = mkClosedRecord $ zipWith (\(i::Int) t -> ("_sub" ++ show i, [t]) ) [1..] subAnns


--showField (nm, args) = nm ++ " : " ++ (show $ map (TP.pretty TP.App) args)

--TODO make tail recursive?
mkAnnot :: [(String, [PatAnn] )] -> Annot PatInfo -> Annot PatInfo
mkAnnot fields otherAnnot = case fields of
  [] -> otherAnnot
  ((ctor, info) :rest) -> (BaseAnnot $ PatData ctor info ) `AnnotUnion` (mkAnnot rest otherAnnot )
  

closedAnnot x = mkAnnot x (Empty)

and = foldr ConstrAnd true
x /\ y = ConstrAnd x y
true = AnnTrue
t1 === t2 = (t1 `Contains` t2 ) /\ (t2 `Contains` t1)

{-

directRecord :: [(String, Type )] -> Type -> Type
directRecord fields restOfRecord = trace ("Direct record " ++ show (map (\(f,x) -> showField (f,[x])) fields )  ) $
  let
    recDict = Map.fromList $ map (\(nm,argTy) -> (nm, [argTy]) ) fields
  in record recDict restOfRecord

-}
