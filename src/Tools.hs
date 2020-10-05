{-# LANGUAGE PackageImports, LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Tools where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

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
getToExecute (HsModule _ _ _ decls _ _) = head $ filter isToExecute decls

isToExecute :: (LHsDecl GhcPs) -> Bool 
isToExecute (L _ (SpliceD _ (SpliceDecl _ (L _ (HsUntypedSplice _ _ _ _)) _ ) )) = True 
isToExecute _ = False

--Gets all the Expr's in an Application 
getValuesInApp :: (LHsExpr GhcPs) -> [HsExpr GhcPs]
getValuesInApp (L _ (HsApp _ lhs rhs)) = (getValuesInApp lhs) ++ (getValuesInApp rhs)
getValuesInApp (L _ (OpApp _ lhs op rhs)) = concat [(getValuesInApp lhs) , (getValuesInApp op) , (getValuesInApp rhs)]
getValuesInApp (L _ expr) = [expr]

--Creates functions to set up the rest of the envrioment with the other defined values
nonCalledFunctionString :: String -> (ScTypes.ModuleInfo) -> String
nonCalledFunctionString name modu = asone
    where othermembers = Map.elems $ Map.delete name modu 
          otherdecls = map (\(FunctionInfo _ decl _ _) -> decl) othermembers
          declsstrings = map (showSDocUnsafe.ppr) otherdecls
          replacednewlines = map (\x -> (map (\t -> if (t == '\n') then ';' else t) x)) declsstrings
          asone = (concat $ intersperse "; " replacednewlines) ++ "; "

{-
--Gives the actual type
eval :: forall t. Typeable t
     => String -> IO (Either Hint.InterpreterError t)
eval s = Hint.runInterpreter $ do
  Hint.setImports ["Prelude"]
  Hint.interpret s (Hint.as :: t) -} 


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