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


qualifier :: String 
qualifier = "definitionGetterqual"

--Given an Expression and the enviroment return the correct rhs to substitute
getDef :: (HsExpr GhcPs) -> [HsExpr GhcPs] -> ScTypes.ModuleInfo -> IO(HsExpr GhcPs)
getDef func args modu = do 
    let funcname = showSDocUnsafe $ ppr $ func -- Get the function name
    (funcdef, t) <- case (modu Map.!? funcname) of --Get the function definition
        Just (FunctionInfo _ (L _ decl) typeSig _) -> return (decl, typeSig) 
        _ -> error $ Tools.errorMessage ++  "funcdef not found : " ++ funcname-- Should never happen


    --Horrible horrible hack (This will be removed in 2.0)
    newtypestr <- case t of --Creating the type for this
        (Just t1) -> do 
            let str = reverse $ dropWhile (\x -> x /= ' ') $ reverse (showSDocUnsafe $ ppr t1)
            
            let result = qualifier ++ str ++ "Int; "

            return $ result
        _ -> return ""

    let (defmap, newfuncdef) = createNewFunction funcdef

    let funcstring = (Tools.nonCalledFunctionString modu) ++ newtypestr ++ (createFunction newfuncdef) -- Create the function

    let stringArgs = map (showSDocUnsafe.ppr) args

    getMatchingDefinition funcstring (qualifier ++ funcname) stringArgs defmap

--Creates a new function, and it's map 
createNewFunction :: (HsDecl GhcPs) -> ((Map.Map Int (HsExpr GhcPs)), (HsDecl GhcPs))
createNewFunction (ValD v (FunBind a b (MG c (L d defs) e ) f g)) = (map, decl)
    where 
        (map, defs') = foldr createNewFunctionCase (Map.empty, []) defs
        decl = (ValD v (FunBind a b (MG c (L d defs') e ) f g)) 

--This is being used for the fold
createNewFunctionCase :: (LMatch GhcPs (LHsExpr GhcPs)) -> ((Map.Map Int (HsExpr GhcPs)), [LMatch GhcPs (LHsExpr GhcPs)]) -> ((Map.Map Int (HsExpr GhcPs)), [LMatch GhcPs (LHsExpr GhcPs)])
createNewFunctionCase  (L l (Match a b c (GRHSs d bodies e) ) ) (m, matches) = (m'', match : matches)
    where 
           firstIndex = Map.size m
           m' = Map.fromList $ zip [firstIndex..] (map getFunctionDefFromBody bodies)
           m'' = Map.union m' m 
           indexedBodies = zip [firstIndex..] bodies 
           bodies' = map subIntegerValue indexedBodies
           match = (L l (Match a b c (GRHSs d bodies' e)))

subIntegerValue :: (Int,(LGRHS GhcPs (LHsExpr GhcPs))) -> (LGRHS GhcPs (LHsExpr GhcPs))
subIntegerValue (val, (L l (GRHS a b (L l' _)) )) = (L l (GRHS a b (L l' def)))
    where def = Tools.stringtoId (show val)

getMatchingDefinition :: String -> String -> [String] -> (Map.Map Int (HsExpr GhcPs)) -> IO (HsExpr GhcPs)
getMatchingDefinition function funcname args defmap = do 
    defNo <- Tools.evalWithArgs @Int function funcname args 
    
    case defNo of 
        (Right i) -> return (defmap Map.! i)
        (Left errs) -> error $ Tools.errorMessage ++ funcname
    
--Creates the function to be executed
createFunction :: (HsDecl GhcPs) -> String
createFunction (ValD _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _)) = intercalate ";" finalCases
        where cases = map (showSDocUnsafe.ppr) defs
              casesNoNewlines = map (\x -> (map (\t -> if (t == '\n') then ' ' else t) x)) cases
              finalCases = map (\x -> qualifier ++ x) casesNoNewlines

--Get all the bodies for one RHS
getFunctionBody :: (LMatch GhcPs (LHsExpr GhcPs)) -> (HsExpr GhcPs)
getFunctionBody (L _ (Match _ _ _ (GRHSs _ bodies _) ) ) | (length bodies == 1 ) = getFunctionDefFromBody $ head bodies
                                                         | otherwise = error "Guards are not currently supported!"
getFunctionBody _ = error $ Tools.errorMessage ++  "Issue getting rhs of function" --Should never happen

--Gets the function definition from the body 
getFunctionDefFromBody :: (LGRHS GhcPs (LHsExpr GhcPs)) -> (HsExpr GhcPs)
getFunctionDefFromBody (L _ (GRHS _ _ (L _ def)) ) = def
getFunctionDefFromBody _ = error $ Tools.errorMessage ++  "Issue getting rhs of function" --Should never happen 