{-# LANGUAGE PackageImports, LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Tools where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" BasicTypes
import "ghc-lib-parser" Config
import "ghc-lib-parser" DynFlags
import "ghc-lib-parser" StringBuffer
import "ghc-lib-parser" Fingerprint
import "ghc-lib-parser" Lexer
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" ErrUtils
import qualified "ghc-lib-parser" Parser
import "ghc-lib-parser" FastString
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" Panic
import "ghc-lib-parser" HscTypes
import "ghc-lib-parser" HeaderInfo
import "ghc-lib-parser" ToolSettings
import "ghc-lib-parser" GHC.Platform
import "ghc-lib-parser" Bag


import Control.Exception (throwIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer (execWriterT, tell)
import Data.Foldable (for_)
import Data.Typeable (Typeable)
import Data.Either
import Data.List
import qualified Data.Map as Map

import ScTypes

import qualified Language.Haskell.Interpreter as Hint

toolsqualifier = "toolsqual"

isFunction :: (LHsDecl GhcPs) -> Bool 
isFunction (L _ (ValD _ (FunBind _ _ _ _ _))) = True 
isFunction _ = False

isType :: (LHsDecl GhcPs) -> Bool 
isType (L _ (SigD _ _)) = True 
isType _ = False

getToExecute :: (HsModule GhcPs) -> (LHsDecl GhcPs)
getToExecute (HsModule _ _ _ decls _ _) = if ((length executables) /= 0) then head executables else error "No statements found to execute."
  where 
     executables = filter isToExecute decls

isToExecute :: (LHsDecl GhcPs) -> Bool 
isToExecute (L _ (SpliceD _ (SpliceDecl _ (L _ (HsUntypedSplice _ _ _ _)) _ ) )) = True 
isToExecute _ = False

--Get the function expr and the argument expressions (In the right order)
getFuncArgs :: (LHsExpr GhcPs) -> (HsExpr GhcPs, [HsExpr GhcPs])
getFuncArgs (L _ (HsApp _ lhs (L _ rhs))) = (func, lhsargs ++ [rhs]) 
  where 
  (func, lhsargs) = getFuncArgs lhs

getFuncArgs (L _ (OpApp _ (L _ lhs) (L _ op) (L _ rhs))) = (removePars op , [lhs, rhs])

getFuncArgs (L l (HsPar _ expr)) = getFuncArgs expr
getFuncArgs (L _ expr) = (expr, [])

--Creates functions to set up the rest of the envrioment with the other defined values
nonCalledFunctionString :: (ScTypes.ModuleInfo) -> String
nonCalledFunctionString modu = concat declsstrings
    where members = Map.elems modu 
          declsstrings = map (\x -> "let { "  ++ (printfunc x) ++ " } in ") members
          asone = (concat $ intersperse "; " declsstrings) ++ "; "

printfunc :: FunctionInfo -> String 
printfunc (FunctionInfo _ (L l decl) (Just t) _) = (showSDocUnsafe $ ppr t ) ++ " ; " ++ (printdecl decl)
printfunc (FunctionInfo _ (L l decl) Nothing _) = (printdecl decl)

printdecl :: (HsDecl GhcPs) -> String
printdecl def@(ValD _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _)) = intercalate ";" $ map (showSDocUnsafe.ppr) defs

--Executes a function when we need to 
--Do all the generation here so we can update this with a better soloution at some point
evalWithArgs :: forall t. Typeable t 
    => String -> String -> [String] -> String -> [String] -> IO (Either Hint.InterpreterError t)
evalWithArgs function funcname args modulepath hide = Hint.runInterpreter $ do 
    Hint.loadModules [modulepath]
    Hint.setImportsF [Hint.ModuleImport "Prelude" Hint.NotQualified (Hint.HidingList hide), Hint.ModuleImport (getModuleName modulepath) Hint.NotQualified Hint.NoImportList]
    Hint.interpret toEx (Hint.as :: t)
    where toEx = function ++ funcname ++ argString
          argString = concat $ " " : intersperse " " args

--Gives output as a string
evalAsString :: String -> String -> [String] -> IO(Either Hint.InterpreterError String)
evalAsString     s modulepath hide = Hint.runInterpreter $ do
  Hint.loadModules [modulepath]
  Hint.setImportsF [Hint.ModuleImport "Prelude" Hint.NotQualified (Hint.HidingList hide), Hint.ModuleImport (getModuleName modulepath) Hint.NotQualified Hint.NoImportList]
  Hint.eval s

  --Takes a string and turns it into the ID of a var
stringtoId :: String -> (HsExpr GhcPs)
stringtoId str = (HsVar NoExtField (noLoc (mkRdrUnqual $ mkVarOcc str)))

errorMessage :: String
errorMessage = "Oops, this shouldn't happen, please send a copy of your input file, and this output to stupid-computer@wasey.net : "

removeLPars :: (LHsExpr GhcPs) -> (LHsExpr GhcPs)
removeLPars (L l expr) = (L l (removePars expr))

--Removes the pars if they exist
removePars :: (HsExpr GhcPs) -> (HsExpr GhcPs)
removePars (HsPar _ (L l (HsVar xvar id))) = (HsVar xvar id)
removePars (HsPar _ (L l (HsLit xlit id))) = (HsLit xlit id)
removePars (HsPar _ (L l (HsPar xpar expr))) = removePars (HsPar xpar expr)
removePars (HsPar _ (L l (HsOverLit xlit lit))) = (HsOverLit xlit lit)
removePars expr = expr

parseModule :: String -> DynFlags -> String -> ParseResult (Located (HsModule GhcPs))
parseModule filename flags str =
  unP Parser.parseModule parseState
  where
    location = mkRealSrcLoc (mkFastString filename) 1 1
    buffer = stringToStringBuffer str
    parseState = mkPState flags buffer location


matchesPattern :: (HsExpr GhcPs) -> String -> (ScTypes.ModuleInfo) -> String -> IO(Bool)
matchesPattern expr pat modu filepath = do 
  let funcname = "matchpat" ++ toolsqualifier
  let funcstring = "let { " ++ ("matchpat"++toolsqualifier++" "++pat ++" = 1; matchpat"++toolsqualifier++" _ = 0;")  ++ " } in "
  let arg = "( " ++ (showSDocUnsafe $ ppr expr) ++ ")"
  
  defNo <- Tools.evalWithArgs @Integer funcstring funcname [arg] filepath (Map.keys modu)
  case defNo of 
    (Right 0) -> return False 
    (Right 1) -> return True 
    _ -> error $ Tools.errorMessage ++ funcname

getDefFromBind :: (LHsBindLR GhcPs GhcPs) -> (HsExpr GhcPs)
getDefFromBind (L _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _)) = getFirstDefMatch $ head defs

getFirstDef :: (LHsDecl GhcPs) -> (HsExpr GhcPs)
getFirstDef (L _ (ValD _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _))) = getFirstDefMatch $ head defs

getFirstDefMatch :: (LMatch GhcPs (LHsExpr GhcPs)) -> (HsExpr GhcPs)
getFirstDefMatch (L _ (Match _ _ _ (GRHSs _ bodies _))) = getFunctionDefFromBody $ head bodies  

--Gets the function definition from the body 
getFunctionDefFromBody :: (LGRHS GhcPs (LHsExpr GhcPs)) -> (HsExpr GhcPs)
getFunctionDefFromBody (L _ (GRHS _ _ (L _ def)) ) = def
getFunctionDefFromBody _ = error $ Tools.errorMessage ++  "Issue getting rhs of function" --Should never happen 

applyArgs :: (HsExpr GhcPs) -> [HsExpr GhcPs] -> (LHsExpr GhcPs)
applyArgs expr [] = (noLoc expr)
applyArgs expr args = foldr (\arg -> (\expr -> noLoc (HsApp NoExtField expr (noLoc arg)))) (noLoc expr) (reverse args)

getModuleName filepath = reverse $ takeWhile (/='/') $ drop 3 $ reverse filepath