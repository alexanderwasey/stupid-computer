{-# LANGUAGE PackageImports #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module PrepStage where

import "ghc-lib-parser" GHC.Hs

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

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
getTypeName _ = error "Trying to get name of non type"

prepFunction :: Map.Map String (LHsDecl GhcPs) -> (LHsDecl GhcPs) -> (ScTypes.FunctionName, ScTypes.FunctionInfo) 
prepFunction typemap decl = (name, (FunctionInfo name decl decltype args))
    where 
        name = getName decl 
        args = numArgs decl
        decltype = typemap Map.!? name

--Gets the name from a function declaration
getName :: (LHsDecl GhcPs) -> ScTypes.FunctionName 
getName (L _ (ValD _ (FunBind _ (L _ name) _ _ _))) = occNameString $ rdrNameOcc name
getName expr = error $ showSDocUnsafe $ ppr expr

--Gets the number of arguments from a function declaration
numArgs :: (LHsDecl GhcPs) -> ScTypes.NoArgs 
numArgs (L _ (ValD _ (FunBind _ _ (MG _ (L _ cases) _) _ _))) = numArgsMatch $ head cases
    where numArgsMatch (L _ (Match _ _ pattern rhs) ) = length pattern
numArgs _ = error "Trying to get number of arguments to non function"