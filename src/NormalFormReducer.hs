{-# LANGUAGE PackageImports, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module NormalFormReducer where 

import "ghc-lib-parser" GHC.Hs

import "ghc-lib-parser" Config
import "ghc-lib-parser" DynFlags
import "ghc-lib-parser" StringBuffer
import "ghc-lib-parser" Fingerprint
import "ghc-lib-parser" Lexer
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" ErrUtils
import qualified "ghc-lib-parser" Parser
import "ghc-lib-parser" FastString
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" Panic
import "ghc-lib-parser" HscTypes
import "ghc-lib-parser" HeaderInfo
import "ghc-lib-parser" ToolSettings
import "ghc-lib-parser" GHC.Platform
import "ghc-lib-parser" Bag


import qualified Data.Map.Strict as Map
import Data.List
import Data.Either

import Tools

reduceNormalForm :: (LHsExpr GhcPs) -> DynFlags -> IO(Maybe (LHsExpr GhcPs))
reduceNormalForm (L l expr) flags = do 
    collapsedexpr <- Tools.evalAsString $ showSDocUnsafe $ ppr expr 
    case collapsedexpr of 
        (Left _) -> return Nothing 
        (Right out) -> do 
            case Tools.parseModule "<normform>" flags out of 
                PFailed _ -> return $ Just (L l (Tools.stringtoId out)) 
                POk _ (L _ (HsModule _ _ _ [(L l(SpliceD _ (SpliceDecl _ (L _ (HsUntypedSplice _ _ _ expr)) _ )))] _ _)) -> do 
                    return $ Just expr
                _ -> error "FATAL REDUCTION ERROR"