{-
Joseph Eremondi
UU# 4229924
APA Project 2
April 17, 2015
-}


{-# LANGUAGE ScopedTypeVariables #-}
module Type.Effect.Expression where

import Control.Applicative ((<$>))
import qualified Control.Monad as Monad
import Control.Monad.Error
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Text.PrettyPrint  as PP

import AST.Literal as Lit
import Reporting.Annotation as Ann hiding (map)
import AST.Expression.General
import qualified AST.Expression.Canonical as Canonical
import qualified AST.Pattern as P
import Reporting.PrettyPrint (pretty)
import qualified Reporting.PrettyPrint as TP
import qualified Reporting.Region as R
import qualified AST.Type as ST
import qualified AST.Variable as V
--import Type.Type hiding (Descriptor(..))
--import Type.Fragment
--import qualified Type.Environment as Env
import qualified Type.Effect.Literal as Literal
import qualified Type.Effect.Pattern as Pattern

import qualified Reporting.Error.Type as RErr

import Data.Char (isUpper)

import Type.Effect.Common

--import Debug.Trace (trace)

nativeOps = map (\n -> V.Canonical (V.Module ["Basics"]) n ) [
  "+"
  ,"-"
  ,"*"
  ,"/"
  ,"%"
  ,"-"
  ,"//"
  ,"*"
  ]

--trace _ x = x

--newVar = varN `fmap` (liftIO $ variable Flexible)

--TODO remove from IO
makeFn t1 t2 = do
  return $ BaseAnnot $ PatLambda t1 t2 

constrain
    :: PatAnnEnv
    -> Canonical.Expr
    -> PatAnn
    -> IO (AnnConstraint PatInfo)
constrain env (A region expr) tipe = do 
    let --list t = Env.get env Env.types "List" $ t
        and = foldr ConstrAnd true
        x /\ y = ConstrAnd x y
        true = AnnTrue
        t1 === t2 = (t1 `Contains` t2 ) /\ (t2 `Contains` t1)
        --t1 ==> t2 = error "BAD LAMBDA TODO"--
         --We override this for our fn def
        --x <? t = (CInstance region x t)
        --clet schemes c = CLet schemes c

        exists :: (Annot info -> IO (AnnConstraint info) ) -> IO (AnnConstraint info)
        exists = existsWith _
        
        --emptyRec = termN EmptyRecord1
        --bool = Env.get env Env.types "Bool"
        --top = Env.get env Env.types "Int"
        isTop t =
          exists $ \restOfRec ->
            return $ (t === (BaseAnnot Top))
        
        
    
    case expr of
      Literal lit -> case lit of
        (IntNum n) -> liftIO $ exists $ \restOfRec ->
          return $ trace "mkAnnot expr" $ tipe === mkAnnot [("_" ++ show n, [])] restOfRec
        (FloatNum f) -> liftIO $ exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show f, [])] restOfRec
        (Chr u) -> liftIO $ exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show u, [])] restOfRec
        (Str s) -> liftIO $ exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show s, [])] restOfRec
        (Boolean b) -> liftIO $ exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show b, [])] restOfRec

      GLShader _uid _src gltipe -> return true --We never pattern match against GLSL shaders


      --Native can be any function, but we always make it a function
      --Meaning for non-function values, we MUST match against it with _
      --This deals with the fact that there are infinite integer constructors
      Var (V.Canonical (V.Module ("Native":_)) _) -> liftIO $  isTop tipe


      --Variable has annotation that we look up in the environment
      Var var -> error "TODO variable? Env?"
          where
            name = V.toString var

      --A range could be empty, so we set its annotation to top
      Range lo hi ->
        liftIO $ exists $ \tlo ->
        exists $ \thi -> do
          --TODO make this safe!
          c1 <- constrain env lo tlo
          c2 <- constrain env hi thi
          isTopConstr <- isTop tipe
          return $ c1 /\ c2 /\ isTopConstr

      --We know that [] is never a cons
      ExplicitList [] -> liftIO $ exists $ \restOfRec ->
        return $ tipe === mkAnnot [("_[]", [])] restOfRec

     --We know that an explicit list that's not empty will start with a cons
      --Then we recursively annotate the rest of the list
      ExplicitList (firstExp:others) ->
        liftIO $ exists $ \restOfRec ->
        exists $ \exprType ->
        exists $ \subListType -> do
          exprConstr <- constrain env firstExp exprType
          subListConstr <-  constrain env (A region $ ExplicitList others) subListType
          let isConsConstr = tipe === mkAnnot [("_::", [exprType, subListType])] restOfRec
          return $ exprConstr /\ subListConstr /\ isConsConstr
      
      --Treat binops just like functions at the type level
      Binop op e1 e2 ->
        if (elem op nativeOps)
        then
          exists $ \t1 ->
          exists $ \t2 -> do
            c1 <- constrain env e1 t1
            c2 <- constrain env e2 t2
            tc <- isTop tipe
            return $ c1 /\ c2 /\ tc
        else do
            let opFn = A region $ Var op
            let fn1 = A region $ App opFn e1
            let fnVersion = A region $ App fn1 e2
            constrain env fnVersion tipe

      --Lambda: we extract the fragment (i.e. variables) from the pattern argument
      --Infer the constraints for the body, given arguments are bound in a scheme
      --Then ensure that the function has annotation {_Lambda  : {_sub1:t1, _sub2:t2 }  }
      --where t1 is the set of valid constructors we can match against for our argument
      --and t2 is the set of constructor values possibly returned by the function
      Lambda p e ->
          exists $ \targ ->
          exists $ \tbody -> do
            fragment <- _ --Pattern.constrain env p targ
            --TODO constrain arg types
            c2 <- constrain env e tbody
            --Make sure the argument type is only the patterns matched
            cMatch <- _ --Pattern.allMatchConstraints env targ region [p]
            --TODO adjust this for annotations
            c <- _ -- return $ ex (vars fragment) (clet [monoscheme (typeEnv fragment)]
                                             --( typeConstraint fragment /\ c2 ))
            fnTy <- makeFn targ tbody
            let retConstr =
                  --TODO fragment
                  {-typeConstraint fragment /\ -} cMatch /\ c /\ (tipe === fnTy) -- fnTy
            return retConstr

      --Nothing fancy here: we ensure the function has a function annotation
      --And that the argument annotation is a subtype of the function argument annotation
      App e1 e2 -> 
          exists $ \t -> do
            fnTy <- makeFn t tipe
            c1 <- constrain env e1 fnTy
            c2 <- constrain env e2 t --TODO where do we speicify direction of subtyping?
            return $ c1 /\ c2

      --TODO not top?
      --We join over multiple branches of an if statement, giving them Top
      --Since there are many potential values they can take on
      MultiIf branches ->  do
        branchConstrs <- mapM constrain' branches
        isTopConstr <- isTop tipe 
        return $ isTopConstr /\ (and branchConstrs) 
          where
              --Ensure each branch has the same type as the overall expr
             --TODO ensure True is in a guard?
             constrain' (b,e) = exists $ \branchType -> (constrain env e branchType )
                  
                  
      --TODO not top?
      --We join over multiple branches of a case statement, giving them Top
      --Since there are many potential values the overall expression
      --Additionally, we ensure that the annotation of the expression matched against
      --Is a subtype of the patterns that can be matched
      --We also do some manipulation with fragments (variables) bound by pattern matches
      Case ex branches ->
          exists $ \restOfRec ->
          exists $ \texp -> do
          --exists $ \tReturn -> do
            --t is the type of the expression we match against 
            ce <- constrain env ex texp
            canMatchConstr <-
                _ --Pattern.allMatchConstraints env texp region (map fst branches)
            --canMatchType <- Pattern.typeForPatList env region (map fst branches)
            let branchConstraints (p,e) =
                  --exists $ \retAnnot -> 
                  exists $ \patType -> do
                    --let recType = _
                    fragment <- _ -- Pattern.constrain  env p patType --texp
                    letConstr <- _ --clet [toScheme fragment] <$> constrain env e tipe 
                    return 
                      $ letConstr  -- /\  tipe === retAnnot --TODO remove?
            joinedBranchConstraints <- mapM branchConstraints branches
            let resultConstr = and joinedBranchConstraints
            --We can get infinite types if we try to combine our branches
            --So we always assume we return top
            --TODO better solution?
            --isTopConstr <- isTop tipe
            return $ ce /\ canMatchConstr /\ resultConstr -- /\ isTopConstr --TODO more precise?


      --A Constructor has a function type, accepting any argument
      --And returning something tagged with (at least) its constructor
      --We also constrain that there exists some (possibly empty) set of other constructors it can take
      --This allows for sub-effecting
      Data rawName [] -> constrainCtor region env rawName tipe

      --We treat constructor application with args as a function call
      Data rawName args -> trace "DATA multi " $ do
        --let name =
        --      if ('.' `elem` rawName)
        --      then rawName
        --      else ("Main." ++ rawName )  --TODO what if not in main?
        exists $ \ctorType -> do
          let ctorExp = (A region $ Data rawName [])
          ctorConstrs <- constrain env ctorExp ctorType
          fnConstrs <- constrain env (foldApp ctorExp args) tipe
          return $ ctorConstrs /\ fnConstrs
        where
          foldApp fn [] = fn
          foldApp fn (arg:argRest) = foldApp (A region $ App fn arg) argRest

      --Let expressions: we iterate through the definitions of the let expression
      --Getting the schemes for each (mutually recursive) definition
      --We constrain the body given the defintions of the let variable
      Let defs body -> --TODO ensure less than pattern type
          do c <- constrain env body tipe
             (schemes, rqs, fqs, header, c2, c1) <-
                 Monad.foldM (constrainDef region env)
                             ([], [], [], Map.empty, true, true)
                             (concatMap expandPattern defs)
             return $ _ --clet schemes
                      --     (clet [Scheme rqs fqs (clet [monoscheme header] c2) header ]
                      --           (c1 /\ c))

      --Since our annotations work on records to begin with, we just do record manipulations
      --Like we would for normal typechecking
      --This is safe, since our annotations use string names that are not syntactically valid in Elm
      --So there will never be name conflicts
      Access e label -> 
        exists $ \recordType ->
        exists $ \restOfRecord -> do
          recordConstr <- constrain env e recordType 
          return $ recordConstr /\ _ --(recordType === (directRecord [(label, tipe)] restOfRecord))
          
      Remove e label ->
        exists $ \originalRecType ->
        exists $ \fieldType -> do
          recordConstr <- constrain env e originalRecType 
          return $ recordConstr /\ _ --(originalRecType === (directRecord [(label, fieldType)] tipe))
        
          
      Insert e label value ->
        exists $ \originalRecType ->
        exists $ \newFieldType -> do
          recordConstr <- constrain env e originalRecType 
          return $ recordConstr /\  _ --(tipe === (directRecord [(label, newFieldType)] originalRecType))

      Modify e fields ->
        exists $ \originalRecType ->
        exists $ \newFieldType ->
        exists $ \restOfRec -> do
          recordConstr <- constrain env e originalRecType 
          fieldNewTypeConstrs <- forM fields $ \(nm, fexp) -> do
            newFieldType <- _ --newVar
            fieldConstr <- constrain env fexp newFieldType 
            return (nm, newFieldType, fieldConstr)
          let fieldTypeConstr = foldr  (\(_,_,c1) c2 -> c1 /\ c2) true fieldNewTypeConstrs
          let fieldTypePairs = map (\(n,t,_) -> (n,t))  fieldNewTypeConstrs
            
          return $
            recordConstr
            /\ fieldTypeConstr
            -- /\(tipe === (directRecord fieldTypePairs restOfRec))
          
      --Recursive: a record with no fields is empty
      --And for a record with fields, we infer the annotation for its field
      --Recursively infer the annotations for the rest of the record
      --And constrain that the result record must have the one field and the rest of the record
      Record fields -> case fields of
        [] -> return $  tipe === (BaseAnnot $ PatOther [])
        ((nm,fexp):others) ->
          exists $ \restOfRec ->
          exists $ \fieldType -> do
            fieldConstr <- constrain env fexp fieldType 
            otherConstr <- constrain env (A region $ Record others) restOfRec 
            return $
              fieldConstr
              /\ otherConstr
              -- /\ tipe === directRecord [(nm, fieldType)] restOfRec



--Constrain a definition
--Most of this is just dealing with schemes
--We ignore any type annotations, since they don't tell us about pattern matching
--Then we generate the constraints for the definition values
--With the defined variables added to their environment
--This is also where we close over schemes, since we have Let polymorphism
--constrainDef :: R.Region -> Env.Environment -> Info -> Canonical.Def
constrainDef region env info (Canonical.Definition pattern expr maybeTipe) = _
{-
    let qs = [] -- should come from the def, but I'm not sure what would live there...
        (schemes, rigidQuantifiers, flexibleQuantifiers, headers, c2, c1) = info
    in
    do rigidVars <- forM qs (\_ -> liftIO $ variable Rigid) -- Some mistake may be happening here.
                                                       -- Currently, qs is always [].
       case pattern of
         (A _ (P.Var name)) -> do
             v <- liftIO $ variable Flexible
             let tipe = varN v
                 inserts = zipWith (\arg typ -> Map.insert arg (varN typ)) qs rigidVars
                 env' = env { Env.value = List.foldl' (\x f -> f x) (Env.value env) inserts }
             c <- constrain env' expr tipe
             return ( schemes
                    , rigidVars ++ rigidQuantifiers
                    , v : flexibleQuantifiers
                    , Map.insert name (A region tipe) headers
                    , c /\ c2
                    , c1 )

         _ -> error ("problem in constrainDef with " ++ show pattern)
-}


--Helper function, was in the original Elm code
expandPattern :: Canonical.Def -> [Canonical.Def]
expandPattern def@(Canonical.Definition pa@(A region pattern) lexpr@(A r _) _maybeType) =
    case pattern of
      P.Var _ -> [def]
      _ -> Canonical.Definition (A region (P.Var x)) lexpr Nothing : map toDef vars --we ignore type sigs
          where
            vars = P.boundVarList pa
            x = "$" ++ concat vars
            mkVar = A r . localVar
            toDef y = Canonical.Definition (A region (P.Var y)) (A r $ Case (mkVar x) [(pa, mkVar y)]) Nothing

--To constrain a constructor
--We get its function type from our environment
--We annotate it as a function which can accept any arguments
--And which is annotated with the given constructor
--And possibly more values
constrainCtor region env rawName tipe = trace "DATA one " $ do
        let qualName =
              if ('.' `elem` rawName)
              then rawName
              else ("Main." ++ rawName )
        --(arity, cvars, args, result) <- liftIO $ freshDataScheme env (V.toString name)
        let ctorDict =_ -- Env.constructor env
        let theKey =
              if Map.member rawName ctorDict
              then rawName
              else if Map.member qualName ctorDict
              then qualName
              else
                let
                  possibleKeys = filter (\k -> List.isSuffixOf rawName k) $ Map.keys ctorDict
                in if (null possibleKeys)
                      then error $ "Name " ++ (show rawName) ++ " not in dict " ++ show (Map.keys ctorDict)
                      else head possibleKeys
        (arity,typeVars,_,_) <- _ -- liftIO $ Env.get env Env.constructor theKey 
        doWithArgTypes typeVars theKey arity []
        where
          
          doWithArgTypes typeVars nm 0 argTypes = _ $ \restOfRecord ->
              do
                let ctorRetType = mkAnnot [("_" ++ nm, argTypes )] restOfRecord
                ctorAnnotation <- makeCtorType (reverse argTypes) ctorRetType
                return _ -- $ CEqual RErr.None region tipe (ctorAnnotation)
          
          doWithArgTypes typeVars nm arity argTypes =
            _ $ \t ->
              doWithArgTypes typeVars nm (arity - 1) (t:argTypes)
          --Constructor take
          makeCtorType [] ret = return ret
          makeCtorType (arg:argRest) ret = do
            fnTy <- makeFn arg ret
            makeCtorType argRest fnTy
          --applyTypeVars [] ty = ty
          --applyTypeVars (var:vars) ty = applyTypeVars vars (ty <| (varN var) )

