{-# LANGUAGE FlexibleInstances #-}
module Type.Effect.Pattern where

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
import qualified Type.Effect.Literal as Literal
import Type.Effect.Common
import qualified Data.List as List

import Debug.Trace (trace)


constrain :: Environment -> P.CanonicalPattern -> Type
          -> ErrorT (A.Region -> PP.Doc) IO Fragment
constrain env pattern tipe = trace "Pattern constr" $ 
    let region = A.None (pretty pattern)
        t1 === t2 = A.A region (CEqual t1 t2)
    in
    case pattern of
      P.Anything -> return emptyFragment

      P.Literal lit -> do
          c <- liftIO $ Literal.constrain env region lit tipe
          return $ emptyFragment { typeConstraint = c }

      P.Var name -> do
          v <- liftIO $ variable Flexible
          return $ Fragment {
              typeEnv    = Map.singleton name (varN v),
              vars       = [v],
              typeConstraint = varN v === tipe
          }

      P.Alias name p -> do
          v <- liftIO $ variable Flexible
          fragment <- constrain env p tipe
          return $ fragment
            { typeEnv = Map.insert name (varN v) (typeEnv fragment)
            , vars    = v : vars fragment
            , typeConstraint = varN v === tipe /\ typeConstraint fragment
            }

      P.Data name patterns -> do
          --TODO is this the right args?
          (kind, cvars, args, result) <- liftIO $ freshDataScheme env (V.toString name)
          fragment <- Monad.liftM joinFragments (Monad.zipWithM (constrain env) patterns args)
          let ourConstr = tipe === closedRecord [("_" ++ show name, args )]
          return $ fragment {
                typeConstraint = typeConstraint fragment /\ ourConstr,
                vars = cvars ++ vars fragment
              }

      P.Record fields -> do
          pairs <- liftIO $ mapM (\name -> (,) name <$> variable Flexible) fields
          let tenv = Map.fromList (map (second varN) pairs)
          c <- exists $ \t -> return (tipe === record (Map.map (:[]) tenv) t)
          return $ Fragment {
              typeEnv        = tenv,
              vars           = map snd pairs,
              typeConstraint = c
          }

instance Error (A.Region -> PP.Doc) where
  noMsg _ = PP.empty
  strMsg str span =
      PP.vcat [ PP.text $ "Type error " ++ show span
              , PP.text str ]
{-
data PatType =
  PatCtor String
  | PatRec
  | PatAnything
    deriving (Eq, Ord)
-}

{-
data OneLevelPat =
  Ctor (String, [P.CanonicalPattern])
  | WildCard
  deriving (Eq)
-}

----Used to sort based on constructor
--sameCtor (Ctor _) (Ctor _) = True
--sameCtor WildCard WildCard = True
--sameCtor _ _ = False


ctorName :: P.CanonicalPattern -> String
ctorName pat = case pat of
  (P.Data name p2) -> "_" ++ show name
  (P.Record p) -> error "TODO record case"
  (P.Alias p1 p2) -> ctorName p2
  (P.Var p) -> "_"
  P.Anything -> "_"
  (P.Literal p) -> "_" ++ show p


--TODO P.record?
{-
patternCtor :: P.CanonicalPattern -> OneLevelPat
patternCtor (P.Data name pats) = Ctor ("_" ++ V.toString name, pats)
patternCtor (P.Literal lit) = Ctor ("_" ++ show lit, [])
patternCtor (P.Alias _ pat) = patternCtor pat
patternCtor P.Anything = WildCard
patternCtor (P.Var _) = WildCard
-}
{-
mergeOneLevel :: OneLevelPat -> OneLevelPat -> OneLevelPat
mergeOneLevel WildCard _ = WildCard
mergeOneLevel _ WildCard = WildCard
mergeOneLevel p1@(Ctor (n1, pl1) ) p2@(Ctor (n2, pl2) ) =
  if n1 == n2
  then Ctor (n1, zipWith (\x y -> [x,y]) pl1 pl2 )
  else error "Can't merge different constructors"
-}


--Group patterns by their constructors, since we might match on more/less specific versions
sortByCtor :: [P.CanonicalPattern] -> [(String, [[P.CanonicalPattern]])]
sortByCtor patList =
  let
    allNames = (List.nub $ map (ctorName) patList)
    maybeAddName name pat subPatList = case pat of
      P.Data name2 pats -> if (name == ctorName pat) then (pats : subPatList) else subPatList
      _ -> error "TODO other cases"
    sortedPats = [ (ctor, List.transpose $ foldr (maybeAddName ctor) [] patList) | ctor <- allNames]
      
  in sortedPats

--Given the list of patterns with the same initial constructor
--Merge them into a single constructor string, and a list of sub-patterns matched
--pats should never be empty

allMatchConstraints
  :: A.Region -> [P.CanonicalPattern] -> Type
    -> ErrorT [PP.Doc] IO TypeConstraint
allMatchConstraints region patList tipe = eachCtorHelper (sortByCtor patList)  
  where
    indexFields = map (\i -> "_" ++ show i) [1..]
    true = A.A region CTrue
    eachCtorHelper []  = return true
    eachCtorHelper ( (ctor, subPats ) : otherPats) =
      exists $ \subType ->
      exists $ \otherFields -> do
        subConsts <- eachArgHelper (zip indexFields subPats) subType
        otherFieldConstr <- eachCtorHelper otherPats
        let ourRecConstr = A.A region $ CEqual tipe (mkRecord [(ctor, [subType])] otherFields )
        return $ subConsts /\ otherFieldConstr /\ ourRecConstr
    eachArgHelper [] tipe = return $ A.A region  $ CEqual tipe emptyRec
    eachArgHelper ((fieldName, argPats) : otherPats) tipe =
      exists $ \otherFields ->
      exists $ \thisArgType -> do
        argConstr <- allMatchConstraints region argPats thisArgType
        otherFieldsConstr <- eachArgHelper otherPats otherFields
        let ourTypeConstr = A.A region $ CEqual thisArgType (mkRecord [(fieldName, [tipe])] otherFields )
        return $ argConstr /\ otherFieldsConstr /\ ourTypeConstr
        
