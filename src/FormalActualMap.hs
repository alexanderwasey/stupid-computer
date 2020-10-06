{-# LANGUAGE PackageImports, LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module FormalActualMap where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" BasicTypes

import Data.Typeable (Typeable)
import Data.Either
import Data.List
import Data.String
import Data.Char

import Tools
import ScTypes

import qualified Data.Map.Strict as Map

--Returns a map of formals to actuals for a given expression and module enviroment
getMap :: (HsExpr GhcPs) -> [HsExpr GhcPs] -> (ScTypes.ModuleInfo) -> IO(Map.Map String (HsExpr GhcPs))
getMap func args modu = do
    let funcname = showSDocUnsafe $ ppr $ func
    (funcdef, typesig) <- case (modu Map.!? funcname) of --Get the function definition
        Just (FunctionInfo _ (L _ decl) sig _) -> return (decl,sig) 
        _ -> error "funcdef not found"

    let stringArgs = map (showSDocUnsafe.ppr) args

    let funcstring = (Tools.nonCalledFunctionString funcname modu) ++ (maybeCreateSignature typesig) ++ (createFunction funcdef args)

    output <- Tools.evalWithArgs @[(String,String)] funcstring funcname stringArgs
    
    output' <- case output of 
        (Right out) -> return out 
        (Left e) -> do
            error $ "Error compiling function, possibly add a type signature!" 

    let convertedout = map (\(a,b) -> (a, Tools.stringtoId b)) $ output'
    return $ Map.fromList $ convertedout 

--Takes the entire definition of a function
createFunction :: (HsDecl GhcPs) -> [HsExpr GhcPs] -> String
createFunction (ValD _ (FunBind _ _ (MG _ (L _ defs) _) _ _)) args = intercalate " ; " cases
    where cases = map (\fun -> (getLHS fun) ++ "= " ++ (createRHS fun args)) defs
createFunction _ _ = error "getPatternNames called on non function"

--Create LHS for the function
getLHS :: (LMatch GhcPs (LHsExpr GhcPs)) -> String --Will need to use the pretty printer for this 
getLHS fun = Tools.split '=' funString
    where funString = showSDocUnsafe $ ppr fun

--Create the RHS 
createRHS :: (LMatch GhcPs (LHsExpr GhcPs))-> [HsExpr GhcPs] -> String 
createRHS (L _ (Match _ _ pattern _) ) args = "[" ++ (intercalate "," $ concat $ map createTuplesFromPairs patargspairs) ++ "]"
    where patargspairs = zip pattern args 

createTuplesFromPairs :: ((LPat GhcPs), HsExpr GhcPs) -> [String]
--In the case nothing is done to the variable by the pattern
createTuplesFromPairs ((L _ (VarPat _ (L _ id))), expr ) = ["(\"" ++ (showSDocUnsafe $ ppr id) ++ "\",\"" ++ (showSDocUnsafe $ ppr expr) ++ "\")"]
createTuplesFromPairs (pattern, _ ) = map (\x -> "(\"" ++ x ++ "\", show " ++ x ++ ")") elements
    where elements = nameFromPatternComponent pattern

--Takes a part of the pattern and returns it's components
nameFromPatternComponent :: (LPat GhcPs) -> [String]
nameFromPatternComponent (L _ (VarPat _ (L _ name))) = [occNameString $ rdrNameOcc name] -- For single strings?
nameFromPatternComponent (L _ (ConPatIn (L _ name) (InfixCon l r))) = (nameFromPatternComponent l) ++ (nameFromPatternComponent r) -- For (x:xs) patterns
nameFromPatternComponent (L _ (ConPatIn (L _ name) (PrefixCon members))) = concat $ map nameFromPatternComponent members -- For constructor patterns
nameFromPatternComponent (L _ (ConPatIn (L _ name) _)) = [occNameString $ rdrNameOcc name]
nameFromPatternComponent (L _ (ParPat _ name)) = nameFromPatternComponent name --Things in parenthesis
nameFromPatternComponent (L _ (TuplePat _ members _)) = concat $ map nameFromPatternComponent members --Tuples
nameFromPatternComponent (L _ (WildPat (NoExtField))) = [] -- For '_' patterns 
nameFromPatternComponent (L _ (LitPat _ _)) = [] -- Literals do not need to be moved in
nameFromPatternComponent (L _ (NPat _ _ _ _)) = []
nameFromPatternComponent (L _ (ListPat _ pats)) = concat $ map nameFromPatternComponent pats
nameFromPatternComponent e = error $ "Unsupported type in pattern matching :" ++ (showSDocUnsafe $ ppr e)

--Get the signature we need to stop crashes :) 
maybeCreateSignature :: (Maybe TypeSig) -> String 
maybeCreateSignature (Just (L l (SigD xsig (TypeSig xtype funname contents)))) = (createSignature (L l (SigD xsig (TypeSig xtype funname contents))) idents) ++ "; "
    where 
        idents = getIdents contents
maybeCreateSignature _ = "" 

--Actualy create the signature
createSignature :: TypeSig -> [String] -> String 
createSignature (L l (SigD xsig (TypeSig xtype funname contents))) idents = showSDocUnsafe $ ppr newsig
    where 
        shows = genAllShows idents 
        swappedContents = swapResult contents -- Swap out the result of the operation for [(String, String)]
        newcontents = applyShows shows swappedContents
        newsig = (SigD xsig (TypeSig xtype funname newcontents))
createSignature _ _ = ""

--Swap out the result of the function with [(String,String)]
swapResult :: (LHsSigWcType GhcPs) -> (LHsSigWcType GhcPs)
swapResult (HsWC a (HsIB b t)) = (HsWC a (HsIB b t'))
    where t' = swapResultInType t

swapResultInType :: (LHsType GhcPs) -> (LHsType GhcPs) --Keep going to the right until we find the 'result' 
swapResultInType (L loc (HsFunTy xfun l r)) = (L loc (HsFunTy xfun l (swapResultInType r)))
swapResultInType (L loc _) = (L loc result)--Found the return type 
    where sType = noLoc (genTypeFromString "String")
          result = (HsListTy NoExtField (noLoc (HsTupleTy NoExtField HsBoxedOrConstraintTuple [sType, sType] )))

--Get the idents from a type
getIdents :: (LHsSigWcType GhcPs) -> [String]
getIdents (HsWC _ (HsIB _ (L l t))) = idents
    where 
        allidents = nub $ getIdentsType t
        idents = filter (\(x:_) -> not $ isUpper x) allidents -- Check to see if a type (Will start with a cap if so)

getIdentsType :: (HsType GhcPs) -> [String]
getIdentsType (HsFunTy _ (L _ l) (L _ r))= (getIdentsType l) ++ (getIdentsType r)
getIdentsType (HsListTy _ (L _ t)) = getIdentsType t
getIdentsType (HsTyVar _ _ (L _ id)) = [occNameString $ rdrNameOcc id] 
getIdentsType (HsParTy _ (L _ t)) = getIdentsType t
getIdentsType (HsTupleTy _ _ lt) = concat $ map (\(L _ t) -> getIdentsType t) lt
getIdentsType (HsAppTy _ (L _ l) (L _ r)) = (getIdentsType l) ++ (getIdentsType r)
getIdentsType e = error $ "Found non supported type: " ++ (showSDocUnsafe $ ppr e)

genAllShows :: [String] -> [LHsType GhcPs]
genAllShows xs = map genShow xs

--Generate a 'Show x' for x 
genShow :: String -> (LHsType GhcPs)
genShow x = noLoc (applyTypes (genTypeFromString "Show") (genTypeFromString x))

--Apply two types
applyTypes :: (HsType GhcPs) -> (HsType GhcPs) -> (HsType GhcPs)
applyTypes x y = (HsAppTy NoExtField (noLoc x) (noLoc y))

--Generates a HsTyVar from a string
genTypeFromString :: String -> (HsType GhcPs)
genTypeFromString s = (HsTyVar NoExtField NotPromoted (noLoc (mkRdrUnqual $ mkVarOcc s)))

--Apply the shows to the type in the sig
applyShows :: [LHsType GhcPs] -> (LHsSigWcType GhcPs) -> (LHsSigWcType GhcPs)
applyShows [] t = t -- In the case there are no shows to apply
applyShows shows (HsWC a (HsIB b t)) = (HsWC a (HsIB b t'))
    where t' = qualList (shows ++ [t])

qualList :: [LHsType GhcPs] -> (LHsType GhcPs)
qualList [x] = x
qualList (x : xs ) = noLoc (HsQualTy NoExtField (noLoc [x]) (qualList xs))

--Set the lhs as qualifying the rhs 
genQualTy :: (HsType GhcPs) -> (HsType GhcPs) -> (HsType GhcPs)
genQualTy context body = (HsQualTy NoExtField (noLoc [noLoc context]) (noLoc body) )