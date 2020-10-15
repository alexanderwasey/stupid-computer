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
checkType :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> IO(Bool)
checkType decl moduinfo = do         
        result <- Tools.evalAsString toExecute 

        case result of 
            (Right _) -> return True 
            (Left _) -> return False

    where maindecl = "main =  " ++ (showSDocUnsafe $ ppr decl) ++ "} in main"
          otherdecls = map (\x -> (map (\t -> if (t == '\n') then ';' else t) x)) (map printfunc (Map.elems moduinfo))
          toExecute = "let { " ++ (intercalate ";" (otherdecls ++ [maindecl]))


printfunc :: FunctionInfo -> String 
printfunc (FunctionInfo _ decl (Just t) _) = (showSDocUnsafe $ ppr t ) ++ " ; " ++ (showSDocUnsafe $ ppr decl)
printfunc (FunctionInfo _ decl Nothing _) = (showSDocUnsafe $ ppr decl)