{-# LANGUAGE PackageImports, LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Tools where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" BasicTypes


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

isFunction :: (LHsDecl GhcPs) -> Bool 
isFunction (L _ (ValD _ (FunBind _ _ _ _ _))) = True 
isFunction _ = False

isType :: (LHsDecl GhcPs) -> Bool 
isType (L _ (SigD _ _)) = True 
isType _ = False

--Split string on character
split :: Char -> String -> String 
split c (x:xs) = if (x == c) then "" else x : (split c xs)
split _ [] = ""

getToExecute :: (HsModule GhcPs) -> (LHsDecl GhcPs)
getToExecute (HsModule _ _ _ decls _ _) = if ((length executables) /= 0) then head executables else error "No statements found to execute."
  where 
     executables = filter isToExecute decls

isToExecute :: (LHsDecl GhcPs) -> Bool 
isToExecute (L _ (SpliceD _ (SpliceDecl _ (L _ (HsUntypedSplice _ _ _ _)) _ ) )) = True 
isToExecute _ = False

--Get the function expr and the argument expressions (In the right order)
getFuncArgs :: (LHsExpr GhcPs) -> (HsExpr GhcPs, [HsExpr GhcPs])
getFuncArgs (L _ (HsApp _ lhs rhs)) = (func, lhsargs ++ (getValuesInApp rhs)) 
  where 
  (func, lhsargs) = getFuncArgs lhs
getFuncArgs (L _ (OpApp _ lhs op rhs)) = (func , concat [args, getValuesInApp lhs, getValuesInApp rhs])
  where 
    (func, args) = getFuncArgs op
getFuncArgs (L l (HsPar _ expr)) = getFuncArgs expr
getFuncArgs (L _ expr) = (expr, [])



--Gets all the Expr's in an Application 
getValuesInApp :: (LHsExpr GhcPs) -> [HsExpr GhcPs]
getValuesInApp (L _ (HsApp _ lhs rhs)) = (getValuesInApp lhs) ++ (getValuesInApp rhs)
getValuesInApp (L _ (OpApp _ lhs op rhs)) = concat [(getValuesInApp lhs) , (getValuesInApp op) , (getValuesInApp rhs)]
getValuesInApp (L _ expr) = [expr]

--Creates functions to set up the rest of the envrioment with the other defined values
nonCalledFunctionString :: (ScTypes.ModuleInfo) -> String
nonCalledFunctionString modu = asone
    where members = Map.elems modu 
          declsstrings = map printfunc members
          asone = (concat $ intersperse "; " declsstrings) ++ "; "

printfunc :: FunctionInfo -> String 
printfunc (FunctionInfo _ (L l decl) (Just t) _) = (showSDocUnsafe $ ppr t ) ++ " ; " ++ (printdecl decl)
printfunc (FunctionInfo _ (L l decl) Nothing _) = (printdecl decl)

printdecl :: (HsDecl GhcPs) -> String
printdecl (ValD _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _)) = intercalate ";" casesNoNewlines
        where cases = map (showSDocUnsafe.ppr) defs
              casesNoNewlines = map (\x -> (map (\t -> if (t == '\n') then ' ' else t) x)) cases

--Executes a function when we need to 
--Do all the generation here so we can update this with a better soloution at some point
evalWithArgs :: forall t. Typeable t 
    => String -> String -> [String] -> IO (Either Hint.InterpreterError t)
evalWithArgs function funcname args = Hint.runInterpreter $ do 
    Hint.setImports ["Prelude"]
    Hint.interpret toEx (Hint.as :: t)
    where toEx = "let { " ++ function ++ " } in " ++ funcname ++ argString
          argString = concat $ " " : intersperse " " args

--Gives output as a string
evalAsString :: String -> IO(Either Hint.InterpreterError String)
evalAsString     s = Hint.runInterpreter $ do
  Hint.setImports ["Prelude"]
  Hint.eval s

  --Takes a string and turns it into the ID of a var
stringtoId :: String -> (HsExpr GhcPs)
stringtoId str = (HsVar NoExtField (noLoc (mkRdrUnqual $ mkVarOcc str)))

errorMessage :: String
errorMessage = "Oops, this shouldn't happen, please send a copy of your input file, and this output to stupid-computer@wasey.net : "

--Removes the pars if they exist
removePars :: (HsExpr GhcPs) -> (HsExpr GhcPs)
removePars (HsPar _ (L l (HsVar xvar id))) = (HsVar xvar id)
removePars (HsPar _ (L l (HsLit xlit id))) = (HsLit xlit id)
removePars (HsPar _ (L l (HsPar xpar expr))) = removePars (HsPar xpar expr)
removePars (HsPar _ (L l (HsOverLit xlit lit))) = (HsOverLit xlit lit)
removePars expr = expr

--Get the args as a string from the pattern
getArgs :: (LMatch GhcPs (LHsExpr GhcPs)) -> String
getArgs (L _ (Match _ _ pattern _)) = funString
    where patnames = map (showSDocUnsafe.ppr) pattern  
          funString = intercalate " " patnames

--Pretty horrid hack
setResultint :: TypeSig -> String
setResultint (L l (SigD d (TypeSig a b sigcontents))) = concat $ intersperse " -> " aslist
        where types = map (showSDocUnsafe.ppr) (init $ getTypesList sigcontents)
              aslist = types ++ ["Int"]
                  
--Get a list of the types in the function 
--Without the typeclasses
getTypesList :: (LHsSigWcType GhcPs) -> [HsType GhcPs]
getTypesList (HsWC _ (HsIB _ (L _ t))) = getTypes t

getTypes :: (HsType GhcPs) -> [HsType GhcPs]
getTypes (HsQualTy _ _ (L _ t)) = getTypes t
getTypes (HsAppTy _ (L _ l) (L _ r)) = getTypes l ++ getTypes r 
getTypes (HsFunTy _ (L _ l) (L _ r)) = getTypes l ++ getTypes r 
getTypes t = [t]

--Generates a HsTyVar from a string
genTypeFromString :: String -> (HsType GhcPs)
genTypeFromString s = (HsTyVar NoExtField NotPromoted (noLoc (mkRdrUnqual $ mkVarOcc s)))

applyFun :: [LHsType GhcPs] -> (LHsType GhcPs)
applyFun [x] = x
applyFun (x:xs) = noLoc (HsFunTy NoExtField x (applyFun xs))
