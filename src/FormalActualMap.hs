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

qualifier :: String 
qualifier = "formalactualfunc"

--Returns a map of formals to actuals for a given expression and module enviroment 
getMap :: (HsExpr GhcPs) -> [HsExpr GhcPs] -> (ScTypes.ModuleInfo) -> IO(Map.Map String (HsExpr GhcPs))
getMap func args modu = do 
    let funcname = showSDocUnsafe $ ppr $ func
    (funcdef, typesig) <- case (modu Map.!? funcname) of --Get the function definition
        Just (FunctionInfo _ (L _ decl) sig _) -> return (decl,sig) 
        _ -> error $ Tools.errorMessage ++  "funcdef not found"

    let defmap = defMap funcdef

    let stringArgs = map (showSDocUnsafe.ppr) args

    --Need to get the correct definition. 
    --In this case, compared to in DefinitionGetter we want the left hand side of the definition, not the right hand side, which is why we can't just use that again. 
    --Though in future that may be rolled together as one, we will see. (This approach is inefficent, but premature optimisation etc etc.)
    let deffuncstring = (Tools.nonCalledFunctionString modu) ++ (createGetDefFunction defmap args funcname)
    defoutput <- Tools.evalWithArgs @Int deffuncstring (qualifier ++ funcname) stringArgs
    defno <- case defoutput of 
        (Right out) -> return out 
        (Left e) -> do 
            error ("Error compiling function, check the type signature of " ++ funcname ++ ". Consider removing type variables, and replacing with explicit types.")
    let def = defmap Map.! defno
    
    --Now need to construct the function for just this definition
     
    changedList <- getChangedArgs funcname  def typesig stringArgs modu

    --Get the arguments that don't need to be changed
    let nonchangedlist = getNonChangedElementsList defmap args defno

    --Combine the two lists and return them as a map
    return $ Map.fromList (changedList ++ nonchangedlist)

getChangedArgs :: String -> (LMatch GhcPs (LHsExpr GhcPs)) -> (Maybe TypeSig) -> [String] -> (ScTypes.ModuleInfo) -> IO([(String, (HsExpr GhcPs))])
getChangedArgs funcname (L _ (Match _ _ pattern _) ) (Just (L _ (SigD _ (TypeSig _ _ sigcontents)))) args modu = do 
    --Get the list of types
    let types = getTypesList sigcontents
    --Zipped list or arguments and types 
    let argtypes = zip3 pattern types args
    let changedargtypes = filter (\(a,_,_) -> valueChanged a) argtypes
    let (changedpattern, changedtypes, changedargs) = unzip3 changedargtypes
    
    --Now have a list of patterns and types that are going to be changed in some way by the function. 
    --So can create the function 
    -- Need to ensure that the typesignature takes into account the TypeClasses and ensures that all of the variables that are changed can be shown. 
    let function = createFunction funcname changedpattern
    let typesig = createSignature funcname changedtypes
    let getargsstring = (Tools.nonCalledFunctionString modu) ++  typesig ++ function

    output <- Tools.evalWithArgs @[(String,String)] getargsstring (qualifier ++ funcname) changedargs
    stringlist <- case output of 
        (Right out) -> return out 
        (Left e) -> do 
            error ("Error compiling function, check the type signature of " ++ funcname ++ ". Consider removing type variables, and replacing with explicit types.")

    return $  map (\(a,b) -> (a, Tools.stringtoId b)) stringlist


--Creates the function
createFunction :: String -> [(LPat GhcPs)] -> String 
createFunction funcname args = qualifier ++ funcname ++ " " ++ (intercalate " " $ map (showSDocUnsafe.ppr) args) ++ " = " ++ (createRHS args)

--Need to finish this
createRHS :: [(LPat GhcPs)] -> String 
createRHS pattern = "[" ++ (intercalate "," (concatMap createTuple pattern))++ "]"

--Returns true if the value will be modified or used
valueChanged :: (LPat GhcPs) -> Bool
valueChanged (L _ (VarPat _ (L _ id))) = False -- In the case of a single variable
valueChanged (L _ (ConPatIn id _)) = not ((showSDocUnsafe $ ppr id) == "[]")
valueChanged _ = True 

createSignature :: String -> [HsType GhcPs] -> String 
createSignature funcname types = (qualifier ++ funcname) ++ " :: " ++ (concat shows) ++ ((showSDocUnsafe.ppr) singletype) ++ " ; "
    where locatedtypes = map (\x -> (noLoc x)) (types ++ [result])
          singletype = applyFun locatedtypes
          sType = noLoc (genTypeFromString "String")
          result = (HsListTy NoExtField (noLoc (HsTupleTy NoExtField HsBoxedOrConstraintTuple [sType, sType] )))

          idents = getIdents singletype
          shows = map (\x -> " Show " ++ x ++ " => ") idents
    
applyFun :: [LHsType GhcPs] -> (LHsType GhcPs)
applyFun [x] = x
applyFun (x:xs) = noLoc (HsFunTy NoExtField x (applyFun xs))

--Get the expressions that are not going to be changed
getNonChangedElementsList :: Map.Map Int (LMatch GhcPs (LHsExpr GhcPs)) -> [HsExpr GhcPs] -> Int -> [(String, (HsExpr GhcPs))]
getNonChangedElementsList fmap args defno = getNonChangedElementsFunc def args 
    where def = fmap Map.! defno

--Get the expressions that are not going to be changed - from a single definition
getNonChangedElementsFunc :: (LMatch GhcPs (LHsExpr GhcPs)) -> [HsExpr GhcPs] -> [(String, (HsExpr GhcPs))]
getNonChangedElementsFunc (L _ (Match _ _ pattern _) ) args = concat $ map createExprTupleFromPair patargspairs
    where 
        patargspairs = zip pattern args

--Create the tuples
createExprTupleFromPair :: ((LPat GhcPs), HsExpr GhcPs) -> [(String, (HsExpr GhcPs))]
createExprTupleFromPair ((L _ (VarPat _ (L _ id))), expr ) = [((showSDocUnsafe $ ppr id), Tools.removePars expr)]
createExprTupleFromPair _ = [] --In this case the expr would be changed so leave it out

--Assigns each possible definition to a number
defMap :: (HsDecl GhcPs) -> Map.Map Int (LMatch GhcPs (LHsExpr GhcPs)) 
defMap (ValD _ (FunBind _ _ (MG _ (L _ defs) _) _ _)) = Map.fromList $ zip [1..] defs
defMap _ = error $ Tools.errorMessage ++  "getPatternNames called on non function"

createGetDefFunction :: Map.Map Int (LMatch GhcPs (LHsExpr GhcPs)) -> [HsExpr GhcPs] -> String -> String 
createGetDefFunction defmap _ name = intercalate " ; " cases 
    where cases = map (\(defno,fun) -> (qualifier ++ name) ++ " " ++(Tools.getArgs fun) ++ " = " ++ (show defno)) (Map.toAscList defmap)

createTuple :: (LPat GhcPs) -> [String]
createTuple pattern = map (\x -> "(\"" ++ x ++ "\", show " ++ x ++ ")") elements
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

getIdents :: (LHsType GhcPs) -> [String] 
getIdents (L _ t) = filter (\(x:_) -> not $ isUpper x) (nub (getIdentsType t)) 

getIdentsType :: (HsType GhcPs) -> [String]
getIdentsType (HsFunTy _ (L _ l) (L _ r))= (getIdentsType l) ++ (getIdentsType r)
getIdentsType (HsListTy _ (L _ t)) = getIdentsType t
getIdentsType (HsTyVar _ _ (L _ id)) = [occNameString $ rdrNameOcc id] 
getIdentsType (HsParTy _ (L _ t)) = getIdentsType t
getIdentsType (HsTupleTy _ _ lt) = concat $ map (\(L _ t) -> getIdentsType t) lt
getIdentsType (HsAppTy _ (L _ l) (L _ r)) = (getIdentsType l) ++ (getIdentsType r)
getIdentsType (HsQualTy _ _ (L _ t)) = getIdentsType t
getIdentsType e = error $ "Found non supported type: " ++ (showSDocUnsafe $ ppr e)

--Generates a HsTyVar from a string
genTypeFromString :: String -> (HsType GhcPs)
genTypeFromString s = (HsTyVar NoExtField NotPromoted (noLoc (mkRdrUnqual $ mkVarOcc s)))

--Get a list of the types in the function 
--Without the typeclasses
getTypesList :: (LHsSigWcType GhcPs) -> [HsType GhcPs]
getTypesList (HsWC _ (HsIB _ (L _ t))) = getTypes t

getTypes :: (HsType GhcPs) -> [HsType GhcPs]
getTypes (HsQualTy _ _ (L _ t)) = getTypes t
getTypes (HsAppTy _ (L _ l) (L _ r)) = getTypes l ++ getTypes r 
getTypes (HsFunTy _ (L _ l) (L _ r)) = getTypes l ++ getTypes r 
getTypes t = [t]