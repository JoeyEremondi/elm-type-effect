

module Type.Inference where

import qualified Data.Map as Map

import qualified Type.Type as T
import qualified Type.Environment as Env
import qualified Type.Constrain.Expression as TcExpr
import qualified Type.Effect.Expression as EfExpr
import qualified Type.Solve as Solve

import qualified AST.Annotation as A
import AST.Module as Module
import AST.Type (CanonicalType)
import qualified AST.Type as AType
import qualified AST.Variable as Var
import Text.PrettyPrint
import qualified Type.State as TS
import qualified Type.ExtraChecks as Check
import qualified Data.List as List
import Control.Arrow (first, second)
import Control.Monad.State (execStateT, forM)
import Control.Monad.Error (ErrorT, runErrorT, liftIO, throwError)
import qualified Type.PrettyPrint as TP
import qualified Type.Fragment as Fragment

import System.IO.Unsafe  -- Possible to switch over to the ST monad instead of
                         -- the IO monad. I don't think that'd be worthwhile.

import Debug.Trace (trace)
--trace _ x = x

infer
  :: Interfaces
  -> CanonicalModule
  -> Either
      [Doc]
      (Map.Map String CanonicalType, Map.Map String CanonicalType)
infer interfaces modul =
  unsafePerformIO $ runErrorT $
    do  (header, constraint) <- genConstraints interfaces modul

        state <- liftIO $ execStateT (Solve.solve constraint) TS.initialState
        
        
        () <- case TS.sHint state of
                hints@(_:_) -> trace "Making Type error" $ throwError hints
                []          -> return ()

        () <- Check.portTypes (program (body modul))

        let header' = Map.delete "::" header
            types = Map.difference (TS.sSavedEnv state) header'

        annots <- case checkTotality interfaces modul of
          Left hints -> throwError hints
          Right ann -> return ann 
        --let annots = Map.empty :: Map.Map String CanonicalType

        typeResult <-  Check.mainType types
        return $ trace ("Annotations: " ++ show annots ) (typeResult, annots)



checkTotality :: Interfaces -> CanonicalModule -> Either [Doc] (Map.Map String CanonicalType)
checkTotality interfaces modul =
  unsafePerformIO  $ runErrorT $
    do  (header, constraint) <- genTotalityConstraints interfaces modul

        state <- trace ("Got constraints " ++ T.showConstr constraint)
                $ liftIO $ execStateT (Solve.solve constraint) TS.initialState
        case TS.sHint state of
                hints@(_:_) -> throwError hints
                []          -> return ()
        let header' = Map.delete "::" header
            types = Map.difference (TS.sSavedEnv state) header'
        Check.toCanon types
        


genTotalityConstraints
    :: Interfaces
    -> CanonicalModule
    -> ErrorT [Doc] IO (Env.TypeDict, T.TypeConstraint)
genTotalityConstraints interfaces modul =
  do
      --We replace the types constructors take with rigid variables
      --Since they a constructor can take any value i.e. it doesn't pattern match
      normalEnv <- liftIO $ Env.initialEnvironment (canonicalizeAdts interfaces modul)
      let (tyNames, oldTypes) = unzip $ Map.toList $ Env.types normalEnv
      --TODO rigid or flex?
      newTypes <- mapM (\_ ->
                        do
                           newVar <- liftIO $ T.variable T.Flexible
                           --TODO is this right?
                           return $ T.varN newVar) oldTypes

      let env = normalEnv {Env.types = Map.fromList $ zip tyNames newTypes }

      fvar <- liftIO $ T.variable T.Flexible
      c <- trace "Going into EfExpr" $ EfExpr.constrain env (program (body modul)) (T.varN fvar) 
      
      ctors <- trace "Done EfExpr?" $ forM (Map.keys (Env.constructor env)) $ \name -> do
                 (_, vars, args, result) <- liftIO $ Env.freshDataScheme env name
                 return (name, (vars, foldr (T.==>) result args))

      importedVars <-  mapM (canonicalizeAnnots env) (Map.toList interfaces)

      

      let allTypes = concat (ctors : importedVars)
          vars = concatMap (fst . snd) allTypes
          header = Map.map snd (Map.fromList allTypes)
          environ = A.noneNoDocs . T.CLet [ T.Scheme vars [] (A.noneNoDocs T.CTrue) header ]

      
      return (header, environ c)

--genConstraints
--    :: 
--    -> Interfaces
--    -> CanonicalModule
--    -> ErrorT [Doc] IO (Env.TypeDict, T.TypeConstraint)
genConstraints interfaces modul =
  do  env <- liftIO $ Env.initialEnvironment (canonicalizeAdts interfaces modul)

      ctors <- forM (Map.keys (Env.constructor env)) $ \name -> do
                 (_, vars, args, result) <- liftIO $ Env.freshDataScheme env name
                 return (name, (vars, foldr (T.==>) result args))

      importedVars <- mapM (canonicalizeValues env) (Map.toList interfaces)

      let allTypes = concat (ctors : importedVars)
          vars = concatMap (fst . snd) allTypes
          header = Map.map snd (Map.fromList allTypes)
          environ = A.noneNoDocs . T.CLet [ T.Scheme vars [] (A.noneNoDocs T.CTrue) header ]

      fvar <- liftIO $ T.variable T.Flexible
      c <- TcExpr.constrain env (program (body modul)) (T.varN fvar)
      return (header, environ c)


canonicalizeValues
    :: Env.Environment
    -> (Module.Name, Interface)
    -> ErrorT [Doc] IO [(String, ([T.Variable], T.Type))]
canonicalizeValues env (moduleName, iface) =
    forM (Map.toList (iTypes iface)) $ \(name,tipe) ->
        do  tipe' <- Env.instantiateType env tipe Map.empty
            return (Module.nameToString moduleName ++ "." ++ name, tipe')


canonicalizeAnnots
    :: Env.Environment
    -> (Module.Name, Interface)
    -> ErrorT [Doc] IO [(String, ([T.Variable], T.Type))]
canonicalizeAnnots env (moduleName, iface) =
    forM (Map.toList (iAnnots iface)) $ \(name,tipe) ->
        do  tipe' <- Env.instantiateType env tipe Map.empty
            return (Module.nameToString moduleName ++ "." ++ name, tipe')

canonicalizeAdts :: Interfaces -> CanonicalModule -> [CanonicalAdt]
canonicalizeAdts interfaces modul =
    localAdts ++ importedAdts
  where
    localAdts :: [CanonicalAdt]
    localAdts = format (Module.names modul, datatypes (body modul))

    importedAdts :: [CanonicalAdt]
    importedAdts = concatMap (format . second iAdts) (Map.toList interfaces)

    format :: (Module.Name, Module.ADTs) -> [CanonicalAdt]
    format (home, adts) =
        map canonical (Map.toList adts)
      where
        canonical :: (String, AdtInfo String) -> CanonicalAdt
        canonical (name, (tvars, ctors)) =
            ( toVar name
            , (tvars, map (first toVar) ctors)
            )

        toVar :: String -> Var.Canonical
        toVar = Var.Canonical (Var.Module home)
