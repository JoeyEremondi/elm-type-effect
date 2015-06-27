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
import Type.Type
import Type.Fragment
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

data AnnotScheme info = SchemeAnnot (Annot info) | AnnForAll AnnVar (AnnotScheme info) | AnnTrue

type AnnEnv info = Map.Map V.Canonical (AnnotScheme info)

--TODO union-find variables?
newtype AnnVar = AnnVar Int

data AnnConstraint info = Contains (Annot info) (Annot info) | ConstrAnd (AnnConstraint info ) (AnnConstraint info)

--Initialize a pool of variables, returning a source of new variables
initialVariablePool :: IO (IO AnnVar)
initialVariablePool = do
  nextVar <- newIORef (0 :: Int)
  return $ do
    retVal <- readIORef nextVar
    writeIORef nextVar $ retVal + 1
    return $ AnnVar retVal

existsWith :: (IO AnnVar) -> (AnnVar -> IO (Annot info) ) -> IO (Annot info)
existsWith varSource f = do
  fresh <- varSource
  f fresh
  

--import Debug.Trace (trace, traceStack)
trace _ x = x

emptyRec = termN EmptyRecord1

mkClosedRecord l = record (Map.fromList l) $ termN EmptyRecord1

subExprType subAnns = mkClosedRecord $ zipWith (\(i::Int) t -> ("_sub" ++ show i, [t]) ) [1..] subAnns


showField (nm, args) = nm ++ " : " ++ (show $ map (TP.pretty TP.App) args)

mkAnnot :: [(String, [Type] )] -> Type -> Type
mkAnnot fields restOfRecord = trace ("Making record " ++ show (map showField fields )  ) $
  let
    recDict = Map.fromList $ map (\(nm,args) -> (nm, [subExprType args]) ) fields
  in record recDict restOfRecord

closedAnnot :: [(String, [Type] )] -> Type
closedAnnot fields = mkAnnot fields (termN EmptyRecord1)

directRecord :: [(String, Type )] -> Type -> Type
directRecord fields restOfRecord = trace ("Direct record " ++ show (map (\(f,x) -> showField (f,[x])) fields )  ) $
  let
    recDict = Map.fromList $ map (\(nm,argTy) -> (nm, [argTy]) ) fields
  in record recDict restOfRecord

