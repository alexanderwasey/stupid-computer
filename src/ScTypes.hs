{-# LANGUAGE PackageImports #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module ScTypes where

import "ghc-lib-parser" GHC.Hs

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

import qualified Data.Map as Map

type ModuleInfo = (Map.Map FunctionName FunctionInfo) 
data FunctionInfo = FunctionInfo {name::FunctionName, definition::(LHsDecl GhcPs), typesig::(Maybe TypeSig),  numargs::NoArgs}
type FunctionName = String
type NoArgs = Int
type TypeSig = (LHsDecl GhcPs)
