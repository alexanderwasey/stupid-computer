{-# LANGUAGE PackageImports, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module NormalFormReducer where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

import qualified Data.Map.Strict as Map
import Data.List
import Data.Either

import Tools

reduceNormalForm :: (LHsExpr GhcPs) -> IO(Maybe (LHsExpr GhcPs))
reduceNormalForm (L l expr) = do 
    collapsedexpr <- Tools.evalAsString $ showSDocUnsafe $ ppr expr 
    case collapsedexpr of 
        (Left _) -> return Nothing 
        (Right out) -> return $ Just (L l (Tools.stringtoId out))
