{-# LANGUAGE PackageImports, LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module DefinitionGetter where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

import Data.Typeable (Typeable)
import Data.Either

import Data.List

import Tools
import ScTypes

import qualified Data.Map.Strict as Map

--Given an Expression and the enviroment return the correct rhs to substitute
getDef :: (HsExpr GhcPs) -> [HsExpr GhcPs] -> ScTypes.ModuleInfo -> IO(HsExpr GhcPs)
getDef func args modu = do 
    let funcname = showSDocUnsafe $ ppr $ func -- Get the function name
    funcdef <- case (modu Map.!? funcname) of --Get the function definition
        Just (FunctionInfo _ (L _ decl) _ _) -> return decl 
        _ -> error "funcdef not found" -- Should never happen

    let funcstring = (Tools.nonCalledFunctionString funcname modu) ++ (createFunction funcdef) -- Create the function
    let defmap = createRHSMap funcdef -- Create the RHS map
    let stringArgs = map (showSDocUnsafe.ppr) args

    getMatchingDefinition funcstring funcname stringArgs defmap

getMatchingDefinition :: String -> String -> [String] -> (Map.Map Int (HsExpr GhcPs)) -> IO (HsExpr GhcPs)
getMatchingDefinition function funcname args defmap = do 
    defNo <- Tools.evalWithArgs @Int function funcname args 
    
    case defNo of 
        (Right i) -> return (defmap Map.! i)
        (Left errs) -> error $ show errs
    
--Creates the function to be executed
createFunction :: (HsDecl GhcPs) -> String
createFunction (ValD _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _)) = intercalate " ; " cases
    where cases = map (\fun -> (getLHS fun) ++ "= " ++ (createRHS fun)) numberedDefs
          numberedDefs = zip [1..] defs

getLHS :: (Int, (LMatch GhcPs (LHsExpr GhcPs))) -> String
getLHS (_, fun) = Tools.split '=' funString
    where funString = showSDocUnsafe $ ppr fun

createRHS :: (Int, (LMatch GhcPs (LHsExpr GhcPs))) -> String
createRHS (i, fun) = show i

createRHSMap :: (HsDecl GhcPs) -> (Map.Map Int (HsExpr GhcPs))
createRHSMap def = Map.fromList $ createRhsTuples def

--Creates a map of RHS and an integer for each
createRhsTuples :: (HsDecl GhcPs) -> [(Int, (HsExpr GhcPs))]
createRhsTuples decl = zip [1..] $ getFunctionBodies decl 

--Get the bodies of a function (We are assuming each pattern only has one rhs)
getFunctionBodies :: (HsDecl GhcPs) -> [HsExpr GhcPs]
getFunctionBodies  (ValD _ (FunBind _ _ (MG _ (L _ defs) _) _ _)) = map getFunctionBody defs

--Get all the bodies for one RHS
getFunctionBody :: (LMatch GhcPs (LHsExpr GhcPs)) -> (HsExpr GhcPs)
getFunctionBody (L _ (Match _ _ _ (GRHSs _ bodies _) ) ) = getFunctionDefFromBody $ head bodies
getFunctionBody _ = error "Issue getting rhs of function"

--Gets the function definition from the body 
getFunctionDefFromBody :: (LGRHS GhcPs (LHsExpr GhcPs)) -> (HsExpr GhcPs)
getFunctionDefFromBody (L _ (GRHS _ _ (L _ def)) ) = def
getFunctionDefFromBody _ = error "Issue getting rhs of function"