module Type.Annotate where

import Control.Arrow (first, second)
import Control.Monad.Except (Except, forM, liftIO, runExceptT, throwError)
import qualified Data.Map as Map
import qualified Data.Traversable as Traverse

import AST.Module as Module
import qualified AST.Type as Type
import qualified AST.Variable as Var
import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Warning as Warning
import qualified Type.Constrain.Expression as TcExpr
import qualified Type.Environment as Env
import qualified Type.Solve as Solve
import qualified Type.State as TS
import qualified Type.Type as T

import qualified Data.List as List

import qualified Type.Effect.Expression as EfExpr
import Text.PrettyPrint

import Reporting.Report as Report
import Reporting.Region as Region

import System.IO.Unsafe
    -- Maybe possible to switch over to ST instead of IO.
    -- I don't think that'd be worthwhile though.

import Debug.Trace (trace)

import Type.Inference
import Type.PrettyPrint


showVar t = show $ pretty App t



errToString (A.A reg p) = Report.toString "" reg (Error.toReport (Map.empty) p) ""



--showConstr :: TypeConstraint -> String
showConstr con = case con of
  T.CTrue -> ""
  T.CSaveEnv -> "SAVE_ENV"
  (T.CEqual _ _  c1 c2) -> (T.showType c1 ) ++ " === " ++ (T.showType c2)
  (T.CAnd conList) -> "\n****" ++ (List.intercalate "\n" $ map showConstr conList)
  (T.CLet schemes c2) -> "Let {{" ++ (List.intercalate "\n" $ map showVar schemes) ++ "}}[[" ++ showConstr c2 ++ "]]"
  (T.CInstance _ c1 c2) -> "INST " ++ c1 ++ " < " ++ T.showType c2
------------------runExceptT
--Added for APA Project 2
------------------
checkTotality
    :: Interfaces
    -> CanonicalModule
    -> ([(Region.Region, Warning.Warning)], Map.Map String Type.Canonical)
checkTotality interfaces modul =
    unsafePerformIO $ do
        (header, constraint) <-
            liftIO (genTotalityConstraints interfaces modul)
        state <-  Solve.solveToState constraint
        let warnings = List.foldr (\ (A.A reg p) soFar ->
                                  case p of
                                    Error.Mismatch m -> [(reg, missingCaseWarning m)] ++ soFar
                                    _ -> soFar) [] (TS.sError state)

        let header' = Map.delete "::" header
        let types = Map.map A.drop (Map.difference (TS.sSavedEnv state) header')

        retDict <- liftIO (Traverse.traverse T.toSrcType types)
        return $ trace (show retDict ) $ (warnings, retDict)
          
    --do  (header, constraint) <- genTotalityConstraints interfaces modul


------------------
--Added for APA Project 2
------------------
genTotalityConstraints
    :: Interfaces
    -> CanonicalModule
    ->  IO (Env.TypeDict, T.TypeConstraint)
genTotalityConstraints interfaces modul =
  do
      
      normalEnv <- Env.initialEnvironment (canonicalizeAdts interfaces modul)
      let (tyNames, oldTypes) = unzip $ Map.toList $ Env.types normalEnv
      newTypes <- mapM (\_ ->
                        do
                           newVar <- liftIO $ T.variable T.Rigid
                           --TODO is this right?
                           return $ T.varN newVar) oldTypes

      let env = normalEnv {Env.types = Map.fromList $ zip tyNames newTypes }

      fvar <- liftIO $ T.variable T.Flexible
      c <-  EfExpr.constrain env (program (body modul)) (T.varN fvar)  
      
      ctors <-  forM (Map.keys (Env.constructor env)) $ \name -> do
                 (_, vars, args, result) <- liftIO $ Env.freshDataScheme env name
                 return (name, (vars, foldr (T.==>) result args))
      --canonicalizeAnnots
      importedVars <-  mapM (canonicalizeAnnots env) (Map.toList interfaces)
      let importedNames = map (\l -> map fst l ) importedVars
      

      let allTypes = concat (ctors : importedVars)
          vars = concatMap (fst . snd) allTypes
          header = Map.map snd (Map.fromList allTypes)
          environ = T.CLet [ T.Scheme vars [] T.CTrue (Map.map (A.A undefined) header) ]

      
      return (header, environ c)




canonicalizeAnnots
    :: Env.Environment
    -> (Module.Name, Interface)
    ->  IO [(String, ([T.Variable], T.Type))]
canonicalizeAnnots env (moduleName, iface) =
    forM (Map.toList (iAnnots iface)) $ \(name,tipe) ->
        do  tipe' <- Env.instantiateType env tipe Map.empty
            return (Module.nameToString moduleName ++ "." ++ name, tipe')

missingCaseWarning :: Error.Mismatch ->  Warning.Warning
missingCaseWarning err = Warning.MissingCase (Error._leftType err ) (Error._rightType err )
