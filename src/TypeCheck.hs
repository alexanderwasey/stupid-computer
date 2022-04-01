{-# LANGUAGE PackageImports, LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module TypeCheck where 

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

import ScTypes
import Tools
import qualified Data.Map as Map
import Data.List

--Simply checks the types
checkType :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> String -> IO(Bool,String)
checkType decl moduinfo filename = do       
        result <- Tools.evalAsString toExecute filename

        case result of 
            (Right s) -> return (True,s)
            (Left e) -> return (False,"")

    where toExecute = "let main =  " ++ (showSDocUnsafe $ ppr decl) ++ " in main"