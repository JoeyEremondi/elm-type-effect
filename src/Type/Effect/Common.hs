{-# LANGUAGE ScopedTypeVariables #-}
module Type.Effect.Common (mkAnnot, closedAnnot, directRecord, emptyRec ) where

import Control.Arrow (second)
import Control.Applicative ((<$>))
import qualified Control.Monad as Monad
import Control.Monad.Error
import qualified Data.Map as Map
import qualified Text.PrettyPrint as PP

import qualified AST.Annotation as A
import qualified AST.Pattern as P
import qualified AST.Variable as V
import AST.PrettyPrint (pretty)
import Type.Type
import Type.Fragment
import Type.Environment as Env
import qualified Type.Constrain.Literal as Literal

import qualified Type.PrettyPrint as TP

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
