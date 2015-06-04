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
import qualified Type.Constrain.Expression as TcExpr
import qualified Type.Environment as Env
import qualified Type.Solve as Solve
import qualified Type.State as TS
import qualified Type.Type as T

import qualified Data.List as List

import qualified Type.Effect.Expression as EfExpr
import Text.PrettyPrint

import Reporting.Report as Report

import System.IO.Unsafe
    -- Maybe possible to switch over to ST instead of IO.
    -- I don't think that'd be worthwhile though.

import Debug.Trace (trace)

import Type.Inference







errToString (A.A reg p) = Report.toString "" reg (Error.toReport (Map.empty) p) ""

------------------runExceptT
--Added for APA Project 2
------------------
checkTotality
    :: Interfaces
    -> CanonicalModule
    -> Except [A.Located Error.Error] (Map.Map String Type.Canonical)
checkTotality interfaces modul =
  either throwError return $ unsafePerformIO $ runExceptT $
    do  (header, constraint) <-
            liftIO (genTotalityConstraints interfaces modul)
        state <- Solve.solve constraint
        --TODO incorporate into Warning system
        let warnings = List.map (\ (A.A reg p) -> Report.toString "" reg (Error.toReport (Map.empty) p) "" ) $ TS.sError state
        case (trace ("Found warnings " ++ show (length warnings )) $ warnings) of
                errorMsgs@(_:_) -> liftIO
                                  $ mapM_
                                  (\p -> putStrLn ("WARNING: " ++ p)) errorMsgs
                []          -> return ()

        let header' = Map.delete "::" header
        let types = Map.map A.drop (Map.difference (TS.sSavedEnv state) header')

        liftIO (Traverse.traverse T.toSrcType types)
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
