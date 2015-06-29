
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
--import qualified Type.Solve as Solve
--import qualified Type.State as TS
import qualified Type.Type as T

import qualified Data.List as List

import qualified Type.Effect.Expression as EfExpr
import Type.Effect.Common
import Text.PrettyPrint

import Reporting.Report as Report
import Reporting.Region as Region

import System.IO.Unsafe
    -- Maybe possible to switch over to ST instead of IO.
    -- I don't think that'd be worthwhile though.

import Debug.Trace (trace)

import Type.Inference
import Type.PrettyPrint

import Type.Effect.Env
import Type.Effect.Solve

import Control.Applicative

import qualified Reporting.PrettyPrint as RPP
import Text.PrettyPrint

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
    -> ([(Region.Region, Warning.Warning)], PatMatchAnnotations)
checkTotality interfaces modul =
    unsafePerformIO $ do
        (constraint, envDict, header) <-
            liftIO (genTotalityConstraints interfaces modul)
        (finalEnv, rawWarnings) <-
          trace ("\n\nConstraint:\n" ++ show (linearizeConstrs constraint) ++ "\n\n" )
                                  $ solve envDict constraint
        let warnings =  map missingCaseWarning rawWarnings
        --let warnings = List.foldr (\ ap@(A.A reg p) soFar ->
        --                          case p of
        --                            Error.Mismatch m -> [(reg, missingCaseWarning m)] ++ soFar
        --                            _ -> error ("\nOTHER ERROR " ++ errToString ap )) [] (TS.sError state)

        let header' = Map.delete "::" header
        let types =  (Map.difference finalEnv header')


        --trace ("\n\n\nFinalEnv " ++ show (Map.keys finalEnv) ++ "\n\nHeader\n" ++ show (Map.keys header') ++"\n\n\n\n"  )
        --retDict <- liftIO (Traverse.traverse T.toSrcType types)
        return $ trace ("\n\n\nGenerated annots: " ++ show types )
          $ (warnings, types)
          
    --do  (header, constraint) <- genTotalityConstraints interfaces modul


------------------
--Added for APA Project 2
------------------
genTotalityConstraints
    :: Interfaces
    -> CanonicalModule
    ->  IO (AnnConstraint PatInfo, PatMatchAnnotations, PatMatchAnnotations)
genTotalityConstraints interfaces modul =
  do

      let modCode = render $ RPP.pretty Map.empty False (program (body modul))
      putStrLn $ "\n\n\n\nModule code\n\n" ++ modCode ++ "\n\n\n"
      normalEnv <- Env.initialEnvironment (canonicalizeAdts interfaces modul)

      ctors <-  forM (Map.keys (Env.constructor normalEnv)) $ \name -> do
                 (_, vars, args, result) <- liftIO $ Env.freshDataScheme normalEnv name
                 return (name, (vars, foldr (T.==>) result args))
      let ctorNames = map fst ctors
      
      
      
      let annotDict = foldl canonicalizeAnnots Map.empty $ Map.toList interfaces
      let (tyNames, oldTypes) = unzip $ Map.toList $ Env.types normalEnv
      newTypes <- mapM (\_ ->
                        do
                           newVar <- liftIO $ T.variable T.Rigid
                           --TODO is this right?
                           return $ T.varN newVar) oldTypes

      let importEnv = normalEnv {Env.types = Map.fromList $ zip tyNames newTypes }
      emptyEnv <- initialEnv normalEnv

      let region = Region.Region (Region.Position 0 0 ) (Region.Position 0 0 ) --TODO real region
      
      ctorTypes <- forM ctorNames (\_ -> VarAnnot <$> newVar emptyEnv )
      ctorConstrs <- forM (zip ctorNames ctorTypes) (\(nm, t) -> EfExpr.constrainCtor region emptyEnv nm t )
      let ctorConstr = Type.Effect.Common.and ctorConstrs
      let ctorFrag = AnnFragment (Map.fromList $ zip ctorNames ctorTypes) [] ctorConstr

      let env = addFragToEnv (emptyEnv {dict = annotDict}) ctorFrag true
      fvar <- VarAnnot `fmap` newVar env
      (constr, topEnv ) <-EfExpr.constrainTopLevel env (program (body modul)) fvar

      return (constr  /\  ctorConstr, topEnv, annotDict)




canonicalizeAnnots
    :: PatMatchAnnotations
    -> (Module.Name, Interface)
    ->  PatMatchAnnotations
canonicalizeAnnots env (moduleName, iface) =
  let
    pairs = Map.toList $ iAnnots iface
    pairsToAdd = map (\ (k, v) -> (Module.nameToString moduleName ++ "." ++ k, v)) pairs
  in Map.union env (Map.fromList pairsToAdd)

missingCaseWarning :: (PatInfo, PatInfo) ->  (Region.Region, Warning.Warning)
missingCaseWarning (p1, p2 ) =
  (Region.Region (Region.Position 0 0 ) (Region.Position 0 0 ),
     Warning.MissingCase p1 p2)
