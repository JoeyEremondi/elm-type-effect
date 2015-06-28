{-
Joseph Eremondi
UU# 4229924
APA Project 2
April 17, 2015
-}


{-# LANGUAGE FlexibleInstances #-}
module Type.Effect.Pattern where

import Control.Arrow (second)
import Control.Applicative ((<$>))
import qualified Control.Monad as Monad
import Control.Monad.Error
import qualified Data.Map as Map
import qualified Text.PrettyPrint as PP

import qualified Reporting.Annotation as A
import qualified Reporting.Region as R
import qualified AST.Pattern as P
import qualified AST.Variable as V
import Reporting.PrettyPrint (pretty)
import qualified Type.Type as TT
--import Type.Fragment
import qualified Type.Environment as Env
import qualified AST.Literal as Literal
import Type.Effect.Common
import qualified Data.List as List
import qualified Data.UnionFind.IO as UF

import qualified Reporting.Error.Type as RErr

import qualified Type.PrettyPrint as TP

import System.IO.Unsafe (unsafePerformIO)

import Type.Effect.Env

--import Debug.Trace (trace)
--trace _ x = x


--Find the annotations that a variable matching a pattern must have
--And return those constraints, along with the "fragment"
--In the Elm type system, fragments contain new variables defined
--By patterns, as well as constraints on them
constrain
    :: PatAnnEnv
    -> P.CanonicalPattern
    -> PatAnn
    -> IO PatFragment          
constrain env (A.A _ pattern) tipe =
    --TODO what is sensible default for here?
    let region = R.Region (R.Position 0 0 ) (R.Position 0 0 ) --_ --A.None (pretty pattern)
        exists = existsWith env
        --newVar = varN `fmap` (liftIO $ variable Flexible)
        --t1 === t2 = CEqual RErr.None region t1 t2
        --genSubTypeConstr :: Type -> [P.CanonicalPattern] -> Int -> TypeConstraint -> TypeConstraint

        --Helper function: given the sub-patterns of a pattern match
        --Generate the fragment with constraints for annotating
        --With their precise values
        --Nothing fancy, really just looping over the patterns
        --And joining their fragments, recusively calling constrain on them
        {-
        genSubTypeConstr :: PatAnn -> [P.CanonicalPattern] -> Int -> PatFragment -> IO PatFragment
        genSubTypeConstr ty patList num frag = do
          let thePatList :: [P.CanonicalPattern]
              thePatList = patList
          case patList of
                [] -> return frag
                (currentPat:rest) -> do
                  fieldAnnot <- VarAnnot <$> newVar env
                  let
                          n :: Int
                          n = num
                  --TODO make this safe?
                  ourFieldFrag <- constrain env currentPat fieldAnnot
                  newConstr <- do
                      --exists $ \restOfRec -> do
                      --exists $ \fieldAnnot -> do
                        let constr = typeConstraint frag 
                        --TODO do we need this, now that we have list?
                        let ourFieldConstr = _ -- ty === (directRecord [("_sub" ++ show n, fieldAnnot)] restOfRec)
                        return $ constr /\ ourFieldConstr
                  let newFrag = joinFragments env [frag, ourFieldFrag {typeConstraint = newConstr}]
                  genSubTypeConstr ty rest (n+1) newFrag
         -}
    in
    case pattern of
      --No constraints when we match anything, no variables either
      P.Anything -> return $ emptyFragment env

      --We know the exact value of a literal
      P.Literal lit -> do
          c <- constrainLiteral env lit tipe
          return $ (emptyFragment env) { typeConstraint = c }

      --Variable: could have any annotations, so use a fresh typeVar
      P.Var name -> do
          v <- newVar env
          return $ AnnFragment {
              typeEnv    = env {dict = Map.singleton name (SchemeAnnot $ VarAnnot v)},
              vars       = [v],
              typeConstraint = VarAnnot v === tipe
          }

      --Alias: just add the name of the pattern to a fragment, then constrain the pattern
      --This is used for things like sort ((x,y) as pair) = if x < y then pair else (y,x)
      P.Alias name p -> do
          v <-  newVar env
          let varType = VarAnnot v
          fragment <- constrain env p tipe
          --TODO this case? Constrain alias?
          return $ fragment
            { typeEnv = env {dict = Map.insert name (SchemeAnnot varType) (dict $ typeEnv fragment) }
             , vars    = v : vars fragment
            , typeConstraint = (VarAnnot v === tipe) /\ typeConstraint fragment
            }

      --Data: go into sub-patterns to extract their fragments
      --And constrain that the final result has the given constructor  
      P.Data name patterns -> do
          --TODO is this the right args?
          (kind, cvars, args, result) <- liftIO $ Env.freshDataScheme (importedInfo env) (V.toString name)
          argTypes <- mapM (\_ -> VarAnnot <$> newVar env) args
          fragment <- (joinFragments env ) <$> Monad.zipWithM (constrain env) patterns argTypes
          --return fragment --TODO right?
          --We don't constrain at all here, since we already did the pattern match check
          --TODO let-expression for special cases?
              
          recordStructureConstr <- do
             argAnnotVars <- mapM (\_ -> VarAnnot <$> newVar env) patterns  
            --exists $ \recordSubType -> do
            --exists $ \restOfRec -> do
             let ctorFieldConstr =
                   tipe `Contains` ( PatData ("_" ++ V.toString name) argAnnotVars )
             
             argTypesFrags <- mapM (\(pat, t) -> constrain env pat t) $ zip patterns argAnnotVars
             let argTypesFrag = joinFragments env argTypesFrags 
             let argTypesConstr = typeConstraint argTypesFrag
             return $ ctorFieldConstr /\ argTypesConstr
             --genSubTypeConstr tipe args 1 $ A.A region CTrue
            --return $ tipe === mkRecord [("_" ++ V.toString name, args )] restOfRec
          
          return $  fragment {
                typeConstraint = typeConstraint fragment /\ recordStructureConstr,
                vars = vars fragment --TODO where get constructor vars?
              }
      --Record : just map each sub-pattern into fields of a record
      P.Record fields -> do
          pairs <- mapM (\name -> do (,) name <$> newVar env) fields
          let tenv = Map.map VarAnnot $ Map.fromList pairs
          let c =  (tipe === (BaseAnnot $ PatRecord tenv emptyAnnot )) --record (Map.map (:[]) tenv) t
          return $ AnnFragment {
              typeEnv        = env {dict = Map.map (SchemeAnnot) tenv},
              vars           = map snd pairs,
              typeConstraint = c
          }

{-
instance Error (R.Region -> PP.Doc) where
  noMsg _ = PP.empty
  strMsg str span =
      PP.vcat [ PP.text $ "Type error " ++ show span
              , PP.text str ]
-}

--Given a pattern, return name of the top constructor in the pattern
ctorName :: P.CanonicalPattern -> String
ctorName (A.A _ pat) = case pat of
  (P.Data name p2) -> "_" ++ V.toString name
  (P.Record p) -> ""
  (P.Alias p1 p2) -> ctorName p2
  (P.Var p) -> "_"
  P.Anything -> "_"
  (P.Literal l) -> "_" ++ showLit l

showLit :: Literal.Literal -> String
showLit lit = case lit of
  (Literal.IntNum i) -> show i
  (Literal.FloatNum f) -> show f 
  (Literal.Chr c) -> show c
  (Literal.Str s) -> show s
  (Literal.Boolean b) -> show b

trace _ x = x

--Group patterns by their constructors, since we might match on more/less specific versions
sortByCtor :: [P.CanonicalPattern] -> [(String, [[P.CanonicalPattern]])]
sortByCtor patList =
  let
    --TODO sort other than by CTOR?
    allNames = (List.nub $ map (ctorName) patList)
    maybeAddName name pa@(A.A _ pat) subPatList = case pat of
      P.Data name2 pats -> if (name == ctorName pa) then (pats : subPatList) else subPatList
      (P.Record e) -> subPatList
      (P.Alias e1 e2) -> maybeAddName name e2 subPatList
      (P.Var e) -> subPatList --Ignor naze these, we should catch this earlier
      P.Anything -> subPatList --Ignore these, we should catch this earlier
      (P.Literal e) -> subPatList
    sortedPats = [ (ctor, List.transpose $ foldr (maybeAddName ctor) [] patList) | ctor <- allNames]
      
  in trace ("ALL NAMES " ++ show allNames ) $ sortedPats

--Check if a pattern can match any expression
--Basically check for a variable or underscore
containsWildcard :: P.CanonicalPattern -> Bool
containsWildcard (A.A _ pat) =
  case pat of
    (P.Alias p1 p2) -> containsWildcard p2
    (P.Var p) -> True
    P.Anything -> True
    _ -> False

--Given an environment, a type of a value to be matched
--Error information, and a list of patterns to match against
--Return the constraint that every possible constructor the value can take
--Must be able to be matched by the patterns
allMatchConstraints env argType region patList = do
  typeCanMatch <- typeForPatList env region patList
  return $ argType `OnlyContains` typeCanMatch



fieldSubset :: (Map.Map String [TT.Type]) -> (Map.Map String [TT.Type]) -> Bool
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

--Generate the annotation of all patterns which can be matched
--By the given list of patterns
typeForPatList
  :: PatAnnEnv -> R.Region -> [P.CanonicalPattern]
    -> IO PatAnn
typeForPatList env region patList = do
  isTotal <- checkIfTotal env patList
  if isTotal
     then trace ("IS TOTAL " ++ show patList) $ VarAnnot <$> newVar env
     else trace ("NOT TOTAL") $ eachCtorHelper (sortByCtor patList)  
  where
    --indexFields = map (\i -> "_sub" ++ show i) ([1..] :: [Int])
    eachCtorHelper []  = return emptyAnnot
    eachCtorHelper ( (ctor, subPats ) : otherPats) =
      do
        subTypes <- mapM (typeForPatList env region) subPats
        otherFields <- eachCtorHelper otherPats
        let ourRec = PatData ctor subTypes --TODO need otherFields?
        return $ BaseAnnot ourRec


--Equality check for types, used for sorting through environments and getting constructor types
type1Equal :: TT.Term1 TT.Type -> TT.Term1 TT.Type -> Bool
type1Equal t1 t2 = case (t1, t2) of
  (TT.App1 t1a t1b, TT.App1 t2a t2b) -> (typeNEqual t1a t2a) && (typeNEqual t1b t2b)
  (TT.Fun1 t1a t1b, TT.App1 t2a t2b) -> (typeNEqual t1a t2a) && (typeNEqual t1b t2b)
  (TT.Var1 t1a, TT.Var1 t2a) -> typeNEqual t1a t2a
  (TT.EmptyRecord1, TT.EmptyRecord1) -> True
  (TT.Record1 fields1 t1b, TT.Record1 fields2 t2b) ->
    (fieldSubset fields1 fields2) && (fieldSubset fields2 fields1) && (typeNEqual t1b t2b)
  _ -> False

--Check if two types are literally identical
--Equality check for types, used for sorting through environments and getting constructor types
typeNEqual :: TT.Type -> TT.Type -> Bool
typeNEqual t1 t2 = trace ("Comparing " ++ (show $ TP.pretty TP.Never t1  ) ++ " and " ++ ((show $ TP.pretty TP.Never t2  ) ) ) $ case (t1, t2) of
  (TT.VarN (Just n1) _, TT.VarN (Just n2) _) -> (fst n1) == (fst n2) --trace "VAR JUST BASE CASE" $ n1 == n2
  (TT.VarN Nothing t1a, TT.VarN Nothing t2a) -> let
      desc1 = unsafePerformIO $ UF.descriptor t1a
      desc2 = unsafePerformIO $ UF.descriptor t2a
    in  trace ("DESCRIPTOR CASE " ++ (show $ TT.name desc1) ++ "   " ++ show (TT.name desc2 )) $ (TT.name desc1 == TT.name desc2)
  (TT.TermN (Just n1) t1, TT.TermN (Just n2) t2) -> trace "TERM JUST BASE CASE" $ (fst n1 == fst n2) && (type1Equal t1 t2)
  (TT.TermN Nothing t1, TT.TermN Nothing t2) -> trace "TERM NOTHING BASE CASE" $  (type1Equal t1 t2)
  _ -> False

isInfiniteLit :: P.CanonicalPattern -> Bool
isInfiniteLit (A.A _ p) = case p of
  P.Literal (Literal.IntNum _) -> True
  P.Literal (Literal.Str _) -> True
  P.Literal (Literal.Chr _) -> True --We assume chars may be infinite, in the case of Unicode
  _ -> False

removeUnderscore :: String -> String
removeUnderscore s = case s of
  [] -> []
  ('_' : s2) -> s2
  _ -> s

--Given a list of patterns, determine if the pattern can match
--any possible value of its type
--This is used to ensure that complete pattern matches can match against Top,
--Even in the case where no wildcard is present
--Since integers have no constructors (only literals), this will never succeed for integers
checkIfTotal
  :: PatAnnEnv
  -> [P.CanonicalPattern]
  -> IO Bool
--Special case: only ever 1 option for pattern matching on a record
--So it doesn't play into our totality calculations
checkIfTotal _ [A.A _ (P.Record _)] = return True
checkIfTotal env rawPatList = trace ("\n\n\n\n\nCHECK IF TOTAL!!!\n" ++ show rawPatList) $ do
  --An integer or string match will never be total
  --TODO bools and such?
  let patList = filter (not . isInfiniteLit) rawPatList
  let hasWildcard = (any containsWildcard patList)
  let sortedPats = trace ("PAT LIST LENGTH " ++ show (length patList) ) $ sortByCtor patList
  let mapGet d k = case Map.lookup k d of
        Nothing -> error $ "Key " ++ show k ++ " not in " ++ show (Map.keys d)
        Just x -> x
  case (patList,hasWildcard) of
    
    (_, True) -> trace ("HAS WILDCARD " ++ show patList) $ return True
    ([], _) -> return False
    (_,False) -> do
      --TODO pattern match on Bool?
      let allCtors = constructor env --TODO need real env?
      let ctorNames = Map.keys allCtors
      
      ctorValues <- mapM liftIO $ Map.elems allCtors
      ourTypeInfo <- liftIO $ mapGet allCtors (removeUnderscore $ trace ("PATLIST SHOW " ++ show patList) $  fst $ head sortedPats) --remove underscore
      let (_,_,_,ourType) = ourTypeInfo
      let
        ctorsForOurType =
                filter (/= "_Tuple1") $
                map fst $
                filter (\(_, (_,_,_,tp)) ->  typeNEqual tp ourType) $ zip ctorNames ctorValues
      
      let tupleNames = filter (List.isPrefixOf "__Tuple") $ map fst sortedPats
      case (trace ("TUPLE NAMES: " ++ show tupleNames) $ tupleNames) of
        (_:_) -> trace ("TUPLE NAMES: " ++ show tupleNames) $ return True
        _ -> do
          let
            --ctorCovered :: Map.Map String [P.CanonicalPattern] -> String -> Bool
            ctorCovered dict ctor  = trace  ("CTORS FOR OUR TYPE: " ++ show ctorsForOurType ) $
                case (Map.lookup ("_" ++ ctor) dict) of
                  Nothing -> return False
                  Just subPats -> List.and `fmap` mapM (checkIfTotal env) subPats
          coveredList <- mapM (ctorCovered $ Map.fromList sortedPats) ctorsForOurType
          return $ trace ("Ctors for our type: " ++ show ctorsForOurType ++ "\nCovered List " ++ show coveredList ) $ List.and coveredList


--Very Boring, constraint rules for literal patterns
--Constrain just like expression literals, but we don't leave the possible set of values open
--This is for cases where we match against a literal and know its exact value
constrainLiteral
  :: PatAnnEnv
  -> Literal.Literal
  -> PatAnn
  -> IO (AnnConstraint PatInfo)
constrainLiteral env lit tipe = case lit of
        (Literal.IntNum n) -> 
          return $ tipe `Contains` PatData ("_" ++ show n) [] 
        (Literal.FloatNum f) -> 
          return $ tipe `Contains` PatData ("_" ++ show f) [] 
        (Literal.Chr u) -> 
          return  $ tipe `Contains` PatData ("_" ++ show u) [] 
        (Literal.Str s) -> 
          return  $ tipe `Contains` PatData ("_" ++ show s) [] 
        (Literal.Boolean b) -> 
          return  $ tipe `Contains` PatData ("_" ++ show b) [] 
