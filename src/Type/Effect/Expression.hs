{-# LANGUAGE ScopedTypeVariables #-}
module Type.Effect.Expression where

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
import qualified Type.PrettyPrint as TP
import qualified AST.Type as ST
import qualified AST.Variable as V
import Type.Type hiding (Descriptor(..))
import Type.Fragment
import qualified Type.Environment as Env
import qualified Type.Effect.Literal as Literal
import qualified Type.Effect.Pattern as Pattern

import Data.Char (isUpper)

import Type.Effect.Common

--import Debug.Trace (trace)

trace _ x = x
t1 =-> t2 = closedAnnot [("_Lambda", [t1, t2])]

constrain
    :: Env.Environment
    -> Canonical.Expr
    -> Type
    -> ErrorT [PP.Doc] IO TypeConstraint
constrain env (A region expr) tipe = trace (" Constrain " ++ (show $ pretty expr)) $
    let list t = Env.get env Env.types "List" <| t
        and = A region . CAnd
        true = A region CTrue
        t1 === t2 = A region (CEqual t1 t2)
        t1 ==> t2 = error "BAD LAMBDA TODO"--
         --We override this for our fn def
        x <? t = A region (CInstance x t)
        clet schemes c = A region (CLet schemes c)
        
        --emptyRec = termN EmptyRecord1
        bool = Env.get env Env.types "Bool"
        top = Env.get env Env.types "Int"
        
        
    in
    case expr of
      Literal lit -> case lit of
        (IntNum n) -> exists $ \restOfRec ->
          return $ trace "mkAnnot expr" $ tipe === mkAnnot [("_" ++ show n, [])] restOfRec
        (FloatNum f) -> exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show f, [])] restOfRec
        (Chr u) -> exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show u, [])] restOfRec
        (Str s) -> exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show s, [])] restOfRec
        (Boolean b) -> exists $ \restOfRec ->
          return $ tipe === mkAnnot [("_" ++ show b, [])] restOfRec

      GLShader _uid _src gltipe -> return true -- "TODO implement"


      Var (V.Canonical (V.Module ("Native":_)) _) -> return true
      --Special case: Native is a Rigid type variable, could be anything
      {-
      Var (V.Canonical (V.Module ("Native":_)) _) -> do
        exists $ \restOfRec -> do
          rigidType <- varN `fmap` (liftIO $ variable Rigid)
          return true --(tipe === rigidType) --TODO constrain native?
        -}

      --TODO need special case here?
      --TODO native?
      Var var
          | name == saveEnvName -> return (A region CSaveEnv)
          | otherwise           -> return (name <? tipe)
          where
            name = V.toString var

      Range lo hi -> return true -- "TODO implement"
      
      ExplicitList exprs -> return true -- "TODO implement"
      
      --Treat binops just like functions at the type level
      --TODO is this okay?
      Binop op e1 e2 -> trace ("BINOP " ++ show e1 ++ "\n" ++ show e2) $ do
        let opFn = A region $ Var op
        let fn1 = A region $ App opFn e1
        let fnVersion = A region $ App fn1 e2
        constrain env fnVersion tipe

      --Nothing fancy goes on here, we just get the annotation for the pattern
      --And the possible constructors for the result, and bind them into a function type
      Lambda p e ->
          exists $ \targ ->
          exists $ \tbody -> do
            fragment <- try region $ Pattern.constrain env p targ
            --TODO constrain arg types
            c2 <- constrain env e tbody
            --Make sure the argument type is only the patterns matched
            cMatch <- Pattern.allMatchConstraints env targ region [p]
            --TODO adjust this for annotations
            c <- return $ ex (vars fragment) (clet [monoscheme (typeEnv fragment)]
                                             ( c2 ))
            let retConstr = typeConstraint fragment /\ cMatch /\ c /\ tipe === (targ =-> tbody)
            return retConstr
          
      App e1 e2 -> 
          exists $ \t -> do
            c1 <- constrain env e1 (t =-> tipe)
            c2 <- constrain env e2 t --TODO where do we speicify direction of subtyping?
            return $ c1 /\ c2

      MultiIf branches ->  and <$> mapM constrain' branches
          where
              --Ensure each branch has the same type as the overall expr
             --TODO ensure True is in a guard?
             constrain' (b,e) = (constrain env e tipe)
                  
                  
      --TODO how does data flow from Exp to Sub-exp when matched ?
      Case ex branches -> trace ("CASE: Type " ++ show (TP.pretty TP.App tipe)) $
          exists $ \texp ->
          exists $ \tReturn -> do
            --t is the type of the expression we match against 
            ce <- constrain env ex texp
            canMatchConstr <-
                Pattern.allMatchConstraints env texp region (map fst branches)
            canMatchType <- Pattern.typeForPatList env region (map fst branches)
            let branchConstraints (p,e) =
                  exists $ \retAnnot -> 
                  exists $ \patType -> do
                    --let recType = _
                    fragment <- try region $ Pattern.constrain  env p patType --texp
                    letConstr <- clet [toScheme fragment] <$> constrain env e retAnnot 
                    return $ letConstr -- /\ retAnnot === tipe
            resultConstr <- and . (:) ce <$> mapM branchConstraints branches
            --We can get infinite types if we try to combine our branches
            --So we always assume we return top
            --TODO better solution?
            return $ canMatchConstr /\ resultConstr /\ (tipe === top) --TODO more precise?


      Data rawName [] -> trace ("DATA single " ++ rawName) $ constrainCtor region env rawName tipe

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

      Let defs body -> --TODO ensure less than pattern type
          do c <- constrain env body tipe
             (schemes, rqs, fqs, header, c2, c1) <-
                 Monad.foldM (constrainDef region env)
                             ([], [], [], Map.empty, true, true)
                             (concatMap expandPattern defs)
             return $ clet schemes
                           (clet [Scheme rqs fqs (clet [monoscheme header] c2) header ]
                                 (c1 /\ c))

      Access e label -> return true -- "TODO implement"
          
      Remove e label -> return true -- "TODO implement"
          
      Insert e label value -> return true -- "TODO implement"

      Modify e fields -> return true -- "TODO implement"
          
      Record fields -> return true -- "TODO implement"

      PortIn _ _ -> return true -- "TODO implement"

      PortOut _ _ signal -> return true -- "TODO implement"

constrainDef region env info (Canonical.Definition pattern expr maybeTipe) =
    let qs = [] -- should come from the def, but I'm not sure what would live there...
        (schemes, rigidQuantifiers, flexibleQuantifiers, headers, c2, c1) = info
    in
    do rigidVars <- forM qs (\_ -> liftIO $ variable Rigid) -- Some mistake may be happening here.
                                                       -- Currently, qs is always [].
       case pattern of
         (P.Var name) -> do
             v <- liftIO $ variable Flexible
             let tipe = varN v
                 inserts = zipWith (\arg typ -> Map.insert arg (varN typ)) qs rigidVars
                 env' = env { Env.value = List.foldl' (\x f -> f x) (Env.value env) inserts }
             c <- constrain env' expr tipe
             return ( schemes
                    , rigidVars ++ rigidQuantifiers
                    , v : flexibleQuantifiers
                    , Map.insert name tipe headers
                    , c /\ c2
                    , c1 )

         _ -> error ("problem in constrainDef with " ++ show pattern)


expandPattern :: Canonical.Def -> [Canonical.Def]
expandPattern def@(Canonical.Definition pattern lexpr@(A r _) _maybeType) =
    case pattern of
      P.Var _ -> [def]
      _ -> Canonical.Definition (P.Var x) lexpr Nothing : map toDef vars --we ignore type sigs
          where
            vars = P.boundVarList pattern
            x = "$" ++ concat vars
            mkVar = A r . localVar
            toDef y = Canonical.Definition (P.Var y) (A r $ Case (mkVar x) [(pattern, mkVar y)]) Nothing


try :: Region -> ErrorT (Region -> PP.Doc) IO a -> ErrorT [PP.Doc] IO a
try region computation =
  do  result <- liftIO $ runErrorT computation
      case result of
        Left err -> throwError [err region]
        Right value -> return value

--TODO how to make this polyvariant?
constrainCtor region env rawName tipe = trace "DATA one " $ do
        let qualName =
              if ('.' `elem` rawName)
              then rawName
              else ("Main." ++ rawName )
        --(arity, cvars, args, result) <- liftIO $ freshDataScheme env (V.toString name)
        let ctorDict = Env.constructor env
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
        (arity,typeVars,_,_) <- liftIO $ Env.get env Env.constructor theKey 
        doWithArgTypes typeVars theKey arity []
        where
          
          doWithArgTypes typeVars nm 0 argTypes =
            exists $ \restOfRecord -> do
            let
              --TODO closed or open?
              ctorRetType nm = mkAnnot [("_" ++ nm, argTypes )] restOfRecord
              ctorAnnotation nm = --applyTypeVars typeVars
                makeCtorType (reverse argTypes) $ ctorRetType nm
            return $ A region $ CEqual tipe (ctorAnnotation nm)
          doWithArgTypes typeVars nm arity argTypes =
            exists $ \t ->
              doWithArgTypes typeVars nm (arity - 1) (t:argTypes)
          --Constructor take
          makeCtorType [] ret = ret
          makeCtorType (arg:argRest) ret = trace "MCT" $ makeCtorType argRest (arg =-> ret)
          --applyTypeVars [] ty = ty
          --applyTypeVars (var:vars) ty = applyTypeVars vars (ty <| (varN var) )
