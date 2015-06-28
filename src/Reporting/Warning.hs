{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module Reporting.Warning where

import Data.Aeson ((.=))
import qualified Data.Aeson as Json
import qualified Text.PrettyPrint as P
import Text.PrettyPrint ((<+>))

import qualified AST.Module as Module
import qualified AST.Type as Type
import qualified Reporting.Annotation as A
import qualified Reporting.PrettyPrint as P
import qualified Reporting.Report as Report

import qualified Data.List as List

import qualified Type.Effect.Common as TypeEffect


-- ALL POSSIBLE WARNINGS

data Warning
    = UnusedImport Module.Name
    | MissingTypeAnnotation String Type.Canonical
    | MissingCase TypeEffect.PatInfo TypeEffect.PatInfo

-- TO STRING

toString :: P.Dealiaser -> String -> String -> A.Located Warning -> String
toString dealiaser location source (A.A region warning) =
    Report.toString location region (toReport dealiaser warning) source


print :: P.Dealiaser -> String -> String -> A.Located Warning -> IO ()
print dealiaser location source (A.A region warning) =
    Report.printWarning location region (toReport dealiaser warning) source


findMissingCases :: P.Dealiaser -> TypeEffect.PatInfo -> TypeEffect.PatInfo -> String
findMissingCases dealiaser t1 t2 = show t1 ++ "\n*******\n" ++ show t2 --TODO fancier?

typeToMatchedCases dealiaser info = "TODO typeToMatchedCases" -- List.intercalate ", " (map (tail . fst) fields)

needsTop t = case t of
  TypeEffect.Top -> True
  --Type.Record fields _ -> not $ null $ filter (\(x,_) -> x == "__Top" || x == "Lambda") fields
  _ -> False

toReport :: P.Dealiaser -> Warning -> Report.Report
toReport dealiaser warning =
  case warning of
    MissingCase t1 t2 ->
      if needsTop t1
      then Report.simple "unmatched pattern" "Function matching a finite number of patterns given an argument with possibly infinite values. (This is likely from matching on Integer or String literals)." "Try writing a wildcard '_' case for your function."
      else
        Report.simple
          "unmatched pattern"
          ("Possible argument constructors not matched in the given function: "
           ++ findMissingCases dealiaser t1 t2)
          ("Matched patterns: " ++ typeToMatchedCases dealiaser t2)
    UnusedImport moduleName ->
        Report.simple
          "unused import"
          ("Module `" ++ Module.nameToString moduleName ++ "` is unused.")
          ""

    MissingTypeAnnotation name inferredType ->
        Report.simple
          "missing type annotation"
          ("Top-level value `" ++ name ++ "` does not have a type annotation.")
          ( "The type annotation you want looks something like this:\n\n"
            ++ P.render (P.nest 4 typeDoc)
          )
      where
        typeDoc =
          P.hang
            (P.text name <+> P.colon)
            4
            (P.pretty dealiaser False inferredType)


-- TO JSON

toJson :: P.Dealiaser -> FilePath -> A.Located Warning -> Json.Value
toJson dealiaser filePath (A.A region warning) =
  let
    (maybeRegion, additionalFields) =
        Report.toJson [] (toReport dealiaser warning)
  in
      Json.object $
        [ "file" .= filePath
        , "region" .= maybe region id maybeRegion
        , "type" .= ("warning" :: String)
        ]
        ++ additionalFields
