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

import qualified Type.PrettyPrint as TP

import Debug.Trace (trace)
--trace _ x = x

constrain :: Environment -> P.CanonicalPattern -> Type
          -> ErrorT (A.Region -> PP.Doc) IO Fragment
constrain env pattern tipe = 
    let region = A.None (pretty pattern)
        newVar = varN `fmap` (liftIO $ variable Flexible)
        t1 === t2 = A.A region (CEqual t1 t2)
        --genSubTypeConstr :: Type -> [P.CanonicalPattern] -> Int -> TypeConstraint -> TypeConstraint
        genSubTypeConstr ty patList num frag = do
          let thePatList :: [P.CanonicalPattern]
              thePatList = patList
          case patList of
                [] -> return frag
                (currentPat:rest) -> do
                  fieldAnnot <- newVar
                  let
                          n :: Int
                          n = num
                  ourFieldFrag <- constrain env currentPat fieldAnnot
                  newConstr <-
                      exists $ \restOfRec -> do
                      --exists $ \fieldAnnot -> do
                        let constr = typeConstraint frag 
                        
                        let ourFieldConstr = ty === (directRecord [("_sub" ++ show n, fieldAnnot)] restOfRec)
                        return $ constr /\ ourFieldConstr
                  let newFrag = joinFragments [frag, ourFieldFrag {typeConstraint = newConstr}]
                  genSubTypeConstr ty rest (n+1) newFrag
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
          let varType = varN v
          fragment <- constrain env p tipe
          --TODO this case? Constrain alias?
          return $ fragment
            { typeEnv = Map.insert name varType (typeEnv fragment)
            , vars    = v : vars fragment
            , typeConstraint = varType === tipe /\ typeConstraint fragment
            }

      P.Data name patterns -> do
          --TODO is this the right args?
          (kind, cvars, args, result) <- liftIO $ freshDataScheme env (V.toString name)
          argTypes <- mapM (\_ -> newVar) args
          fragment <- Monad.liftM joinFragments (Monad.zipWithM (constrain env) patterns argTypes)
          return fragment --TODO right?
          --We don't constrain at all here, since we already did the pattern match check
          --TODO let-expression for special cases?
          {-    
          recordStructureConstr <-
            exists $ \recordSubType ->
            exists $ \restOfRec -> do
             let ctorFieldConstr =
                   tipe === directRecord [("_" ++ V.toString name, recordSubType )] restOfRec
             
             argTypesFrag <- genSubTypeConstr recordSubType patterns 1 emptyFragment
             let argTypesConstr = typeConstraint argTypesFrag
             return $ ctorFieldConstr /\ argTypesConstr
             --genSubTypeConstr tipe args 1 $ A.A region CTrue
            --return $ tipe === mkRecord [("_" ++ V.toString name, args )] restOfRec
          
          return $ fragment {
                typeConstraint = typeConstraint fragment /\ recordStructureConstr,
                vars = cvars ++ vars fragment
              }
          -}
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
  (P.Data name p2) -> "_" ++ V.toString name
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
    --TODO sort other than by CTOR?
    allNames = (List.nub $ map (ctorName) patList)
    maybeAddName name pat subPatList = case pat of
      P.Data name2 pats -> if (name == ctorName pat) then (pats : subPatList) else subPatList
      (P.Record e) -> subPatList
      (P.Alias e1 e2) -> maybeAddName name e2 subPatList
      (P.Var e) -> subPatList --Ignor naze these, we should catch this earlier
      P.Anything -> subPatList --Ignore these, we should catch this earlier
      (P.Literal e) -> subPatList
    sortedPats = [ (ctor, List.transpose $ foldr (maybeAddName ctor) [] patList) | ctor <- allNames]
      
  in sortedPats

containsWildcard :: P.CanonicalPattern -> Bool
containsWildcard pat =
  case pat of
    (P.Alias p1 p2) -> containsWildcard p2
    (P.Var p) -> True
    P.Anything -> True
    _ -> False

--Given the list of patterns with the same initial constructor
--Merge them into a single constructor string, and a list of sub-patterns matched
--pats should never be empty

allMatchConstraints env argType region patList = do
  typeCanMatch <- typeForPatList env region patList
  return $ trace ("!!! Pattern match type : " ++ show (TP.pretty TP.App typeCanMatch) ) $ (argType === typeCanMatch)
    where t1 === t2 = A.A region (CEqual t1 t2)


fieldSubset :: (Map.Map String [Type]) -> (Map.Map String [Type]) -> Bool
fieldSubset f1 f2 =
  let
    names1 = Map.keys f1
    f2Values = map (\n -> (n, Map.lookup n f2)) names1
    valueGood v = case v of
      (_, Nothing) -> False
      (n, Just t2) ->
        let
          t1 = case Map.lookup n f1 of
            Nothing -> error $ "Key " ++ show n ++ " not in map " ++ show (Map.keys f1)
            Just x -> x
          pairWise = List.all (uncurry typeNEqual) $ zip t1 t2
        in (length t1 == length t2) && pairWise
  in List.all valueGood f2Values

type1Equal :: Term1 Type -> Term1 Type -> Bool
type1Equal t1 t2 = case (t1, t2) of
  (App1 t1a t1b, App1 t2a t2b) -> (typeNEqual t1a t2a) && (typeNEqual t1b t2b)
  (Fun1 t1a t1b, App1 t2a t2b) -> (typeNEqual t1a t2a) && (typeNEqual t1b t2b)
  (Var1 _, Var1 _) -> True
  (EmptyRecord1, EmptyRecord1) -> True
  (Record1 fields1 t1b, Record1 fields2 t2b) ->
    (fieldSubset fields1 fields2) && (fieldSubset fields2 fields1) && (typeNEqual t1b t2b)
  _ -> False

--Check if two types are literally identical
typeNEqual :: Type -> Type -> Bool
typeNEqual t1 t2 = trace ("Comparing " ++ (show $ TP.pretty TP.Never t1  ) ++ " and " ++ ((show $ TP.pretty TP.Never t2  ) ) ) $ case (t1, t2) of
  (VarN v1 t1, VarN v2 t2) -> True 
  (TermN v1 t1, TermN v2 t2) -> {-(v1 == v2) && -}  (type1Equal t1 t2)
  _ -> False

--toMain s = if (elem '.' s) then s else ("Main." ++ s)

checkIfTotal
  :: Environment
  -> [P.CanonicalPattern]
  -> ErrorT [PP.Doc] IO Bool
checkIfTotal env [] = error "ERROR: can't have Case expression with no patterns"
checkIfTotal env patList = do
  let hasWildcard = (any containsWildcard patList)
  let sortedPats = sortByCtor patList
  let mapGet d k = case Map.lookup k d of
        Nothing -> error $ "Key " ++ show k ++ " not in " ++ show (Map.keys d)
        Just x -> x
  case hasWildcard of
    True -> trace ("HAS WILDCARD " ++ show patList) $ return True
    False -> do
      let allCtors = constructor env
      let ctorNames = Map.keys allCtors
      let tupleNames = filter (List.isPrefixOf "_Tuple") ctorNames
      case tupleNames of
        (_:_) -> return True
        _ -> do
          ctorValues <- mapM liftIO $ Map.elems allCtors
          ourTypeInfo <- trace ("Ctor names " ++ show ctorNames ++ "\nmap Keys " ++ show (Map.keys allCtors) ) $ liftIO $ mapGet allCtors (tail $ fst $ head sortedPats) --remove underscore
          let (_,_,_,ourType) = ourTypeInfo
          let
            ctorsForOurType =
                filter (/= "_Tuple1") $
                map fst $
                filter (\(nm, (_,_,_,tp)) -> typeNEqual tp ourType) $ zip ctorNames ctorValues
      
          let
            --ctorCovered :: Map.Map String [P.CanonicalPattern] -> String -> Bool
            ctorCovered dict ctor  =
                case (Map.lookup ("_" ++ ctor) dict) of
                  Nothing -> return False
                  Just subPats -> List.and `fmap` mapM (checkIfTotal env) subPats
          coveredList <- mapM (ctorCovered $ Map.fromList sortedPats) ctorsForOurType
          return $ trace ("Ctors for our type: " ++ show ctorsForOurType ++ "\nCovered List " ++ show coveredList ) $ List.and coveredList

typeForPatList
  :: Environment -> A.Region -> [P.CanonicalPattern]
    -> ErrorT [PP.Doc] IO Type
typeForPatList env region patList = do
  isTotal <- checkIfTotal env patList
  if isTotal
     then trace ("IS TOTAL " ++ show patList) $ anyVar
     else trace ("NOT TOTAL") $ eachCtorHelper (sortByCtor patList)  
  where
    anyVar = do
      newVar <- liftIO $ variable Flexible
      return $ varN newVar
    --indexFields = map (\i -> "_sub" ++ show i) ([1..] :: [Int])
    true = A.A region CTrue
    eachCtorHelper []  = return emptyRec
    eachCtorHelper ( (ctor, subPats ) : otherPats) =
      do
        subTypes <- mapM (typeForPatList env region) subPats
        otherFields <- eachCtorHelper otherPats
        let ourRec = (trace "mkAnnot1" $ mkAnnot [(ctor, subTypes)] otherFields )
        return ourRec -- $ subConsts /\ otherFieldConstr /\ ourRecConstr

    {-eachArgHelper [] = return emptyRec
    eachArgHelper ((fieldName, argPats) : otherPats) =
      do
        thisArgType <- typeForPatList region argPats
        otherFields <- eachArgHelper otherPats
        return   (directRecord [(fieldName, thisArgType)] otherFields ) -}
        
