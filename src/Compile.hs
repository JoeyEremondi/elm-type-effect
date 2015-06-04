module Compile (compile) where

import qualified Data.Map as Map

import Control.Monad (forM)
import qualified AST.Module as Module
import qualified Canonicalize
import Elm.Utils ((|>))
import qualified Nitpick.TopLevelTypes as Nitpick
import qualified Parse.Helpers as Parse
import qualified Parse.Parse as Parse
import qualified Reporting.Error as Error
import qualified Reporting.Result as Result
import qualified Reporting.Report as Report
import qualified Reporting.Region as Region
import qualified Reporting.Warning as Warning
import qualified Type.Inference as TI
import qualified Type.Annotate as TA

import Debug.Trace (trace)

compile
    :: String
    -> String
    -> Bool
    -> Module.Interfaces
    -> String
    -> Result.Result Warning.Warning Error.Error Module.CanonicalModule

compile user projectName isRoot interfaces source =
  do
      -- determine if default imports should be added
      -- only elm-lang/core is exempt
      let needsDefaults =
            not (user == "elm-lang" && projectName == "core")

      -- Parse the source code
      validModule <-
          Result.mapError Error.Syntax $
            Parse.program needsDefaults isRoot (getOpTable interfaces) source

      -- Canonicalize all variables, pinning down where they came from.
      canonicalModule <-
          Canonicalize.module' interfaces validModule

      -- Run type inference on the program.
      types <-
          Result.from Error.Type $
            TI.infer interfaces canonicalModule

      --Get warnings from our type-effect system
      let (warnings ,annots) =
            TA.checkTotality interfaces canonicalModule
      --Apply each warning
      forM warnings (\ (reg, warning) ->
                       trace ("\n" ++ "Line " ++ (show $ Region.line $ Region.start reg)
                              ++ ", col " ++ (show $ Region.column $ Region.start reg) ++ "\n"
                              ++ (Report.toString "" reg (Warning.toReport Map.empty warning) "") ++ "\n" ) $
                       Result.warn reg warning)

      -- One last round of checks
      Result.mapError Error.Type $
        Nitpick.topLevelTypes types (Module.body validModule)

      -- Add the real list of types
      let body = (Module.body canonicalModule) { Module.types = types, Module.annots = annots }

      return $ canonicalModule { Module.body = body }


getOpTable :: Module.Interfaces -> Parse.OpTable
getOpTable interfaces =
  Map.elems interfaces
    |> concatMap Module.iFixities
    |> map (\(assoc,lvl,op) -> (op,(lvl,assoc)))
    |> Map.fromList
