{-# LANGUAGE PackageImports #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module PrepStage where

import "ghc-lib-parser" GHC.Hs

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" DynFlags
import "ghc-lib-parser" BasicTypes


import qualified Data.Map as Map

import ScTypes
import Tools

prepModule :: (HsModule GhcPs) -> (ScTypes.ModuleInfo)
prepModule (HsModule _ _ _ decls _ _) = Map.fromList $ map (prepFunction typedecls) functionbodies
    where 
        functionbodies = filter Tools.isFunction decls
        typedecls = getTypeNames $ filter Tools.isType decls

getTypeNames :: [LHsDecl GhcPs] -> Map.Map String (LHsDecl GhcPs)
getTypeNames types = Map.fromList $ map (\x -> (getTypeName x, x)) types

getTypeName :: (LHsDecl GhcPs) -> String
getTypeName (L _ (SigD _ (TypeSig _ parts _))) = showSDocUnsafe $ ppr $ head parts 
getTypeName _ = error $ Tools.errorMessage ++ "Err getting name of type" 

prepFunction :: Map.Map String (LHsDecl GhcPs) -> (LHsDecl GhcPs) -> (ScTypes.FunctionName, ScTypes.FunctionInfo) 
prepFunction typemap decl = (name, (FunctionInfo name decl' decltype numargs))
    where 
        decl' = ensureInfix decl
        name = getName decl' 
        numargs = numArgs decl'
        decltype = typemap Map.!? name

ensureInfix :: (LHsDecl GhcPs) -> (LHsDecl GhcPs)
ensureInfix (L a (ValD b (FunBind c d (MG e (L f matches) g) h i))) = (L a (ValD b (FunBind c d (MG e (L f matches') g) h i)))
    where matches' = map toPrefix matches
          toPrefix (L l (Match a (FunRhs name _ src) c d)) = (L l (Match a (FunRhs name Prefix src) c d))


--Gets the name from a function declaration
getName :: (LHsDecl GhcPs) -> ScTypes.FunctionName 
getName (L _ (ValD _ (FunBind _ (L _ name) _ _ _))) = occNameString $ rdrNameOcc name
getName expr = error $ showSDocUnsafe $ ppr expr

--Gets the number of arguments from a function declaration
numArgs :: (LHsDecl GhcPs) -> ScTypes.NoArgs 
numArgs (L _ (ValD _ (FunBind _ _ (MG _ (L _ cases) _) _ _))) = numArgsMatch $ head cases
    where numArgsMatch (L _ (Match _ _ pattern rhs) ) = toInteger $ length pattern
numArgs _ = error $ Tools.errorMessage ++ "Getting number of arguments"

prepBind :: (LHsBindLR GhcPs GhcPs)  -> ScTypes.ModuleInfo
prepBind (L l def@(FunBind _ _ function _ _))  = Map.fromList $ [PrepStage.prepFunction Map.empty (L l (ValD NoExtField def))]