{-# LANGUAGE ScopedTypeVariables #-}
module Type.Effect.Common (mkAnnot, closedAnnot, directRecord, emptyRec, constraintOccursCheck ) where

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

import qualified Data.List as List
import qualified Data.UnionFind.IO as UF

import qualified Type.PrettyPrint as TP

import Debug.Trace (trace, traceStack)
--trace _ x = x

emptyRec = termN EmptyRecord1

mkClosedRecord l = record (Map.fromList l) $ termN EmptyRecord1

subExprType subAnns = mkClosedRecord $ zipWith (\(i::Int) t -> ("_sub" ++ show i, [t]) ) [1..] subAnns


showField (nm, args) = nm ++ " : " ++ (show $ map (TP.pretty TP.App) args)

mkAnnot :: [(String, [Type] )] -> Type -> Type
mkAnnot fields restOfRecord = traceStack ("Making record " ++ show (map showField fields )  ) $
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




occursCheck t1 t2 = do
  good1 <- oneSideOccurs t1 t2
  good2 <- oneSideOccurs t2 t1
  return $ good1 && good2


getVarUnifs :: Environment -> TypeConstraint -> [(Variable, Variable)]
getVarUnifs env (A.A _ constr) = case constr of
  (CEqual (VarN _ v1) (VarN _ v2)) -> [(v1, v2)]
  (CAnd l) -> concatMap (getVarUnifs env) l
  (CLet c1 c2) -> (concatMap (getVarUnifs env) $ map constraint c1 ) ++ (getVarUnifs env) c2
  CInstance c1 s -> []
  _ -> []

--Simplified version of unification
constraintOccursCheck :: Environment -> TypeConstraint -> IO Bool
constraintOccursCheck env annCon@(A.A _ constr) = do
  let unifPairs = getVarUnifs env annCon
  trace ("NUM var unifs: " ++ show (length unifPairs)) $ mapM_ (uncurry UF.union) unifPairs
  case constr of
    CTrue -> return True
    CSaveEnv -> return True
    (CEqual t1 t2) -> do
      occursCheck t1 t2
    (CAnd cList) -> List.and `fmap` mapM (constraintOccursCheck env) cList
    (CLet c1 c2) -> do
      good1 <- constraintOccursCheck env c2
      good2 <- List.and `fmap` mapM (constraintOccursCheck env) (map constraint c1 )
      return $ good1 && good2
    (CInstance c1 c2) -> return True
  

oneSideOccurs t1 t2 = trace ("Comparing " ++ show (TP.pretty TP.Never t1) ++ " and " ++ show (TP.pretty TP.Never t2) ) $
  case (t1, t2) of
    (VarN _ var, VarN _ var2) -> do
      UF.union var var2
      return True
    (VarN _ var, _) -> do
      let subTys = getSubVars t2
      occurs <- mapM (UF.equivalent var) subTys
      trace ("OCCURS: " ++ show occurs) $return $ not $ List.or occurs
    _ -> return True


  
  

getSubVars :: Type -> [Variable]
getSubVars t = trace ("\n\nGettng sub vars of " ++ show (TP.pretty TP.Never t)) $ case t of
  TermN _ t -> getSub1Vars t
  VarN _ v -> [v]

getSub1Vars :: Term1 Type -> [Variable]
getSub1Vars ty = case ty of
  (App1 t1 t2) -> (getSubVars t1) ++ (getSubVars t2)
  (Fun1 t1 t2) -> (getSubVars t1) ++ (getSubVars t2)
  (Var1 t) -> getSubVars t
  EmptyRecord1 -> []
  (Record1 t1 t2) -> (concatMap getSubVars $ concat $  Map.elems t1) ++ (getSubVars t2)
