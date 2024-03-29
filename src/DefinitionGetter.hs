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
qualifier = "definitiongetterqual"

--Given an Expression and the enviroment return the correct rhs to substitute
getDef :: (HsExpr GhcPs) -> [HsExpr GhcPs] -> ScTypes.ModuleInfo -> String -> IO(Maybe(HsExpr GhcPs, [LPat GhcPs], Map.Map Integer [LPat GhcPs]))
getDef func args modu filename = do 

    let funcname = showSDocUnsafe $ ppr $ func -- Get the function name
    let funcname' = if ((head funcname ) == '(') then init $ tail funcname else funcname

    (funcdef, t) <- case (modu Map.!? funcname') of --Get the function definition
        Just functioninfo -> do 
            let (L _ info) = definition functioninfo
            return (info, typesig functioninfo) 
        _ -> error $ Tools.errorMessage ++  "funcdef not found : " ++ funcname-- Should never happen
    
    --Create the type for the new function
    newtypestr <- case t of --Creating the type for this
        (Just t1) -> do 
            let t2 = qualifier ++ funcname ++ " :: " ++ (Tools.setResultint t1) ++ ";"
            return t2
        _ -> return ""

    let (defmap, newfuncdef) = createNewFunction funcdef

    let funcstringwithtype = (Tools.nonCalledFunctionString modu) ++ " let { " ++ newtypestr ++ (createFunction newfuncdef) ++ "} in "
    let funcstring = (Tools.nonCalledFunctionString modu) ++ " let { " ++ (createFunction newfuncdef) ++ "} in "-- Create the function (and the map)

    let stringArgs = map (\x -> "( " ++(showSDocUnsafe $ ppr x) ++ ") ") args


    --Only use the type created if it is needed
    resultNoType <- getMatchingDefinition funcstring (qualifier ++ funcname) stringArgs defmap filename (Map.keys modu)
    case resultNoType of 
        Nothing -> getMatchingDefinition funcstringwithtype (qualifier ++ funcname) stringArgs defmap filename (Map.keys modu)
        result -> return result

--Creates a new function, and it's map 
createNewFunction :: (HsDecl GhcPs) -> ((Map.Map Integer ((HsExpr GhcPs), [LPat GhcPs])), (HsDecl GhcPs))
createNewFunction (ValD v (FunBind a b (MG c (L d defs) e ) f g)) = (map, decl)
    where 
        (map, defs') = foldr createNewFunctionCase (Map.empty, []) defs
        decl = (ValD v (FunBind a b (MG c (L d defs') e ) f g)) 

--This is being used for the fold
--Being folded as need to look at the old map in order to keep track of the ordering
createNewFunctionCase :: (LMatch GhcPs (LHsExpr GhcPs)) -> ((Map.Map Integer ((HsExpr GhcPs), [LPat GhcPs])), [LMatch GhcPs (LHsExpr GhcPs)]) -> ((Map.Map Integer ((HsExpr GhcPs), [LPat GhcPs])), [LMatch GhcPs (LHsExpr GhcPs)])
createNewFunctionCase (L l (Match m_ext m_ctxt m_pats (GRHSs d bodies e) ) ) (m, matches) = (m'', match : matches)
    where 
           firstIndex = toInteger $ Map.size m
           m' = Map.fromList $ zip [firstIndex..] $ map (\x -> (x,m_pats)) (map Tools.getFunctionDefFromBody bodies)
           m'' = Map.union m' m 
           indexedBodies = zip [firstIndex..] bodies 
           bodies' = map subIntegerValue indexedBodies
           match = (L l (Match m_ext m_ctxt m_pats (GRHSs d bodies' e)))

subIntegerValue :: (Integer,(LGRHS GhcPs (LHsExpr GhcPs))) -> (LGRHS GhcPs (LHsExpr GhcPs))
subIntegerValue (val, (L l (GRHS a b (L l' _)) )) = (L l (GRHS a b (L l' def)))
    where def = Tools.stringtoId (show val)

getMatchingDefinition :: String -> String -> [String] -> (Map.Map Integer ((HsExpr GhcPs), [LPat GhcPs])) -> String -> [String] -> IO (Maybe(HsExpr GhcPs, [LPat GhcPs], Map.Map Integer [LPat GhcPs]))
getMatchingDefinition function funcname args defmap filename hide = do 
    let pats = Map.map snd defmap

    --Don't bother with any of this if only one definition
    if (length defmap == 1) then do 
        let (expr, pat) = head $ Map.elems defmap
        return $ Just (expr, pat, pats)
    else do 
        defNo <- Tools.evalWithArgs @Integer function funcname args filename hide 
        
        case defNo of 
            (Right i) -> do 
                let (expr, pat) = (defmap Map.! i)
                return $ Just (expr, pat, pats)
            (Left errs) -> return Nothing
    
--Creates the function to be executed
createFunction :: (HsDecl GhcPs) -> String
createFunction (ValD _ (FunBind _ _ (MG _ (L _ defs) _ ) _ _)) = intercalate ";" finalCases
        where cases = map (showSDocUnsafe.ppr) defs
              casesNoNewlines = map (\x -> (map (\t -> if (t == '\n') then ' ' else t) x)) cases
              finalCases = map (qualifier ++) casesNoNewlines

