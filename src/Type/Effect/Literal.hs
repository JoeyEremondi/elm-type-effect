module Type.Effect.Literal where

import Control.Applicative ((<$>))
import qualified Control.Monad as Monad
import Control.Monad.Error
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Text.PrettyPrint as PP

import AST.Literal as Lit
import AST.Annotation as Ann
import AST.Expression.General
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Pattern as P
import AST.PrettyPrint (pretty)
import qualified AST.Type as ST
import qualified AST.Variable as V
import Type.Type hiding (Descriptor(..))
import Type.Fragment
import qualified Type.Environment as Env

import Type.Effect.Common

import Debug.Trace (trace)

constrain env region lit tipe =
  let
    t1 === t2 = A region (CEqual t1 t2)
  in case lit of
        (IntNum n) -> 
          return $ tipe === closedRecord [("_" ++ show n, [])] 
        (FloatNum f) -> 
          return $ tipe === closedRecord [("_" ++ show f, [])] 
        (Chr u) -> 
          return $ tipe === closedRecord [("_" ++ show u, [])] 
        (Str s) -> 
          return $ tipe === closedRecord [("_" ++ show s, [])] 
        (Boolean b) -> 
          return $ tipe === closedRecord [("_" ++ show b, [])] 
