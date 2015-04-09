{-# LANGUAGE ScopedTypeVariables #-}
module Type.Effect.Common (mkRecord, closedRecord, directRecord, emptyRec ) where

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

--import Debug.Trace (trace)
trace _ x = x

emptyRec = termN EmptyRecord1

mkClosedRecord l = record (Map.fromList l) $ termN EmptyRecord1

subExprType subAnns = mkClosedRecord $ zipWith (\(i::Int) t -> ("_sub" ++ show i, [t]) ) [1..] subAnns


mkRecord :: [(String, [Type] )] -> Type -> Type
mkRecord fields restOfRecord =
  let
    recDict = Map.fromList $ map (\(nm,args) -> (nm, [subExprType args]) ) fields
  in record recDict restOfRecord

closedRecord :: [(String, [Type] )] -> Type
closedRecord fields = mkRecord fields (termN EmptyRecord1)

directRecord :: [(String, Type )] -> Type -> Type
directRecord fields restOfRecord =
  let
    recDict = Map.fromList $ map (\(nm,argTy) -> (nm, [argTy]) ) fields
  in record recDict restOfRecord
