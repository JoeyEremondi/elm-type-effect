{-
Joseph Eremondi
UU# 4229924
APA Project 2
April 17, 2015
-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}


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
--import Type.Environment as Env
--import qualified Type.Constrain.Literal as Literal

import qualified Data.List as List
import qualified Data.UnionFind.IO as UF

import qualified Type.PrettyPrint as TP
import qualified Type.State as TS

import Data.IORef

import Data.Ord (comparing)

import qualified Data.UnionFind.IO as UF

import Control.Applicative

import Data.Binary

import Debug.Trace (trace)
import AST.Type as AT

import System.IO.Unsafe

--Generic data type for type annotations
data Annot info =
  BaseAnnot info
  | Empty
  | VarAnnot (AnnVar info)
  | Union (Annot info) (Annot info)
  deriving (Eq, Ord, Show)


data AnnotScheme info = SchemeAnnot (Annot info) | AnnForAll [AnnVar info] (AnnConstraint info ) (Annot info)
  deriving (Show)


--TODO union-find variables?
newtype AnnVar info = AnnVar (Int, UF.Point (Int, Maybe PatInfo) )

instance Eq (AnnVar info) where
  (AnnVar (x,_)) == (AnnVar (y,_)) = x == y

instance Ord (AnnVar info) where
  (AnnVar (x,_)) < (AnnVar (y,_)) = x < y

instance Show (AnnVar info) where
  show (AnnVar (i,uf)) =
    if i < 0
      then show i
      else show $ unsafePerformIO $ UF.descriptor uf

instance Read (AnnVar PatInfo) where
  readsPrec _ (sh:st) =  [(AnnVar ((-1 * read [sh] :: Int), error "Should never use the UF for imported vars"), st)]

deriving instance Read (Annot PatInfo)
deriving instance Read (AnnotScheme PatInfo)
deriving instance Read (AnnConstraint PatInfo)

readDict :: String -> (Map.Map String (AnnotScheme PatInfo))
readDict s = read s

{-
instance Binary PatMatchAnnotations where
  put = put . show
  get = readDict <$> (Data.Binary.get :: Get String)
-}
annotPut :: PatMatchAnnotations -> Put
annotPut = put . toTypes --put :: PatMatchAnnotations -> Put

annotGet :: Get PatMatchAnnotations
annotGet = fromTypes <$> (Data.Binary.get )

data AnnConstraint info =
  Contains (Annot info) info
  | Unify (Annot info) (Annot info)
  | ConstrAnd (AnnConstraint info ) (AnnConstraint info)
  -- | InstanceOf (Annot info) (AnnotScheme info)
  | AnnTrue
  | OnlyContains (Annot info) (Annot info)
  | GeneralizedContains (Annot info) (Annot info)
    deriving (Show)

linearizeConstrs c = case c of
        ConstrAnd c1 c2 -> (linearizeConstrs c1) ++ (linearizeConstrs c2)
        AnnTrue -> []
        --Turn instances into unification when we can
        --InstanceOf c1 (SchemeAnnot c2 ) -> [Unify c1 c2]
        _ -> [c] 
            
constrNum :: AnnConstraint info -> Int
constrNum (AnnTrue) = -1
constrNum (Unify _ _) = 0
--constrNum (InstanceOf _ _) = 1
constrNum (Contains _ _) = 2
constrNum (OnlyContains _ _ ) = 3

--Order for constraints, used in solving
orderConstrs :: AnnConstraint info -> AnnConstraint info -> Ordering
orderConstrs = comparing constrNum

getUF (AnnVar (_, uf)) = uf

      

--Info specific to exhaustiveness-analysis
data PatInfo =
  PatLambda PatAnn PatAnn
  | PatData String [PatAnn]
  | PatRecord (Map.Map String PatAnn) PatAnn
--  | PatOther [PatAnn] --TODO need this?
  | Top
  | NativeAnnot
--  | PatUnInit
  | MultiPat (Map.Map String [PatAnn])
  deriving (Show, Read)

type PatAnn = Annot PatInfo



patUnInit = MultiPat Map.empty

emptyAnnot = Empty --BaseAnnot $ PatOther []

--import Debug.Trace (trace, traceStack)


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


{-

directRecord :: [(String, Type )] -> Type -> Type
directRecord fields restOfRecord = trace ("Direct record " ++ show (map (\(f,x) -> showField (f,[x])) fields )  ) $
  let
    recDict = Map.fromList $ map (\(nm,argTy) -> (nm, [argTy]) ) fields
  in record recDict restOfRecord

-}


type PatMatchAnnotations =  (Map.Map String (AnnotScheme PatInfo))


toCanonicalAnnot :: PatAnn -> AT.Canonical
toCanonicalAnnot (BaseAnnot ann) = toCanonical ann
toCanonicalAnnot Empty = Var "**Empty"
toCanonicalAnnot (VarAnnot (AnnVar (i, _))) = App (Var "**Var") [(Var $ show i )]
toCanonicalAnnot (Union ann1 ann2) = App (Var "**Union" ) [toCanonicalAnnot ann1, toCanonicalAnnot ann2]

toCanonical :: PatInfo -> AT.Canonical
toCanonical (PatLambda info1 info2) = AT.Lambda (toCanonicalAnnot info1) (toCanonicalAnnot info2)
toCanonical (PatData s subs) = AT.App (Var s) (map toCanonicalAnnot subs )
toCanonical (PatRecord fields rest) =
  AT.Record (Map.toList $ Map.map toCanonicalAnnot fields) (Just $ toCanonicalAnnot rest) 
toCanonical Top  = AT.Var "**Top"
toCanonical NativeAnnot = AT.Var "**NativeAnnot"
toCanonical (MultiPat fields) =
  AT.App (Var "**Multi") $
    [AT.Record (Map.toList $ Map.map (\l -> AT.App (Var "**List") (map toCanonicalAnnot l)) fields ) Nothing]

toCanonicalScheme :: AnnotScheme PatInfo -> AT.Canonical
toCanonicalScheme (SchemeAnnot annot) = toCanonicalAnnot annot
toCanonicalScheme (AnnForAll vars _ annot) =
  App
    (App (Var "**VarList") (map (\(AnnVar (i, _))  -> Var (show i ) ) vars ) )
    [toCanonicalAnnot annot]

canonToAnn :: AT.Canonical -> PatAnn
canonToAnn (Var "**Empty" ) = Empty
canonToAnn (App (Var "**Var") [(Var si )]) = VarAnnot $ AnnVar ((-1 * read si) :: Int, error $ "Should never access desc " ++ show si)
canonToAnn (App (Var "**Union" ) [ann1,  ann2]) =
  Union (canonToAnn ann1) (canonToAnn ann2) 
canonToAnn c = BaseAnnot $ canonToInfo c

canonToInfo :: AT.Canonical -> PatInfo
canonToInfo (AT.Lambda i1 i2) = PatLambda (canonToAnn i1) (canonToAnn i2)
canonToInfo (AT.Var "**Top") = Top
canonToInfo (AT.App (Var "**Multi") [AT.Record subs _]) =
  MultiPat $ Map.map (\ (App (Var "**List" ) subs ) -> map canonToAnn subs) $ Map.fromList subs
canonToInfo (AT.App (Var s) subs ) = PatData s $ map canonToAnn subs
canonToInfo (AT.Record subs rest) =
  PatRecord (Map.map canonToAnn $ Map.fromList subs )
    (case rest of
          Just r -> canonToAnn r
          _ -> Empty)

canonToScheme (App (App (Var  "**VarList") vars ) [annot] ) =
  AnnForAll
    (map (\ (Var si) ->  AnnVar (-1 * (read si) :: Int, error $ "Read binary: Should never access desc, " ++ si) ) vars )
    true (canonToAnn annot)
canonToScheme c = SchemeAnnot $ canonToAnn c

toTypes :: PatMatchAnnotations -> Map.Map String AT.Canonical
toTypes = Map.map toCanonicalScheme

fromTypes :: Map.Map String AT.Canonical -> PatMatchAnnotations 
fromTypes = Map.map canonToScheme
