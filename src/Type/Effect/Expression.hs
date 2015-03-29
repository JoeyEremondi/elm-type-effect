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
import qualified AST.Type as ST
import qualified AST.Variable as V
import Type.Type hiding (Descriptor(..))
import Type.Fragment
import qualified Type.Environment as Env
import qualified Type.Effect.Literal as Literal
import qualified Type.Effect.Pattern as Pattern


constrain
    :: Env.Environment
    -> Canonical.Expr
    -> Type
    -> ErrorT [PP.Doc] IO TypeConstraint
constrain env (A region expr) tipe =
    let list t = Env.get env Env.types "List" <| t
        and = A region . CAnd
        true = A region CTrue
        t1 === t2 = A region (CEqual t1 t2)
        x <? t = A region (CInstance x t)
        clet schemes c = A region (CLet schemes c)
        mkRecord l = record (Map.fromList l) $ termN EmptyRecord1
        emptyRec = termN EmptyRecord1
        bool = Env.get env Env.types "Bool"
        top = Env.get env Env.types "Int"
    in
    case expr of
      Literal lit -> case lit of
        (IntNum n) -> return $ tipe === mkRecord [("_" ++ show n, [emptyRec])]
        (FloatNum f) -> return $ tipe === mkRecord [("_" ++ show f, [emptyRec])]
        (Chr u) -> return $ tipe === mkRecord [("_" ++ show u, [emptyRec])]
        (Str s) -> return $ tipe === mkRecord [("_" ++ show s, [emptyRec])]
        (Boolean b) -> return $ tipe === mkRecord [("_" ++ show b, [emptyRec])]

      GLShader _uid _src gltipe -> error "TODO implement"

      --TODO need special case here?
      --TODO native?
      Var var
          | name == saveEnvName -> return (A region CSaveEnv)
          | otherwise           -> return (name <? tipe)
          where
            name = V.toString var

      Range lo hi -> error "TODO implement"
      
      ExplicitList exprs -> error "TODO implement"
      
      Binop op e1 e2 -> error "TODO implement"
          
      Lambda p e ->
          exists $ \t1 ->
          exists $ \t2 -> do
            fragment <- error "TODO Pattern Constraint"--try region $ Pattern.constrain env p t1
            c2 <- constrain env e t2
            let c = ex (vars fragment) (clet [monoscheme (typeEnv fragment)]
                                             (typeConstraint fragment /\ c2 ))
            return $ c /\ tipe === (t1 ==> t2)
          
      App e1 e2 -> 
          exists $ \t -> do
            c1 <- constrain env e1 (t ==> tipe)
            c2 <- constrain env e2 t 
            return $ c1 /\ c2


          
      MultiIf branches -> error "TODO implement"
      
      Case exp branches -> error "TODO implement"
          
      Data name exprs -> error "TODO implement"

      Access e label -> error "TODO implement"
          
      Remove e label -> error "TODO implement"
          
      Insert e label value -> error "TODO implement"

      Modify e fields -> error "TODO implement"
          
      Record fields -> error "TODO implement"

      Let defs body -> error "TODO implement"
      
      PortIn _ _ -> error "TODO implement"

      PortOut _ _ signal -> error "TODO implement"

constrainDef env info (Canonical.Definition pattern expr maybeTipe) =
    let qs = [] -- should come from the def, but I'm not sure what would live there...
        (schemes, rigidQuantifiers, flexibleQuantifiers, headers, c2, c1) = info
    in
    do rigidVars <- forM qs (\_ -> liftIO $ variable Rigid) -- Some mistake may be happening here.
                                                       -- Currently, qs is always [].
       case (pattern, maybeTipe) of
         (P.Var name, Just tipe) -> do
             flexiVars <- forM qs (\_ -> liftIO $ variable Flexible)
             let inserts = zipWith (\arg typ -> Map.insert arg (varN typ)) qs flexiVars
                 env' = env { Env.value = List.foldl' (\x f -> f x) (Env.value env) inserts }
             (vars, typ) <- Env.instantiateType env tipe Map.empty
             let scheme = Scheme { rigidQuantifiers = [],
                                   flexibleQuantifiers = flexiVars ++ vars,
                                   constraint = Ann.noneNoDocs CTrue,
                                   header = Map.singleton name typ }
             c <- constrain env' expr typ
             return ( scheme : schemes
                    , rigidQuantifiers
                    , flexibleQuantifiers
                    , headers
                    , c2
                    , fl rigidVars c /\ c1 )

         (P.Var name, Nothing) -> do
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
expandPattern def@(Canonical.Definition pattern lexpr@(A r _) maybeType) =
    case pattern of
      P.Var _ -> [def]
      _ -> Canonical.Definition (P.Var x) lexpr maybeType : map toDef vars
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


