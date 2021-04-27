{-# LANGUAGE PackageImports #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Main (main) where

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

import System.IO.Extra
import System.Environment

import qualified Language.Haskell.Interpreter as Hint

import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.List 
import Data.Char

import qualified Tools as Tools
import PrepStage
import TypeCheck
import EvalStage
import ScTypes

fakeSettings :: Settings
fakeSettings = Settings
  { sGhcNameVersion=ghcNameVersion
  , sFileSettings=fileSettings
  , sTargetPlatform=platform
  , sPlatformMisc=platformMisc
  , sPlatformConstants=platformConstants
  , sToolSettings=toolSettings
  }
  where
    toolSettings = ToolSettings {
      toolSettings_opt_P_fingerprint=fingerprint0
      }
    fileSettings = FileSettings {}
    platformMisc = PlatformMisc {}
    ghcNameVersion =
      GhcNameVersion{ghcNameVersion_programName="ghc"
                    ,ghcNameVersion_projectVersion=cProjectVersion
                    }
    platform =
      Platform{
        platformWordSize=PW8
      , platformMini=PlatformMini {platformMini_arch=ArchUnknown, platformMini_os=OSUnknown}
      , platformUnregisterised=True
      }
    platformConstants =
      PlatformConstants{pc_DYNAMIC_BY_DEFAULT=False,pc_WORD_SIZE=8}

fakeLlvmConfig :: LlvmConfig
fakeLlvmConfig = LlvmConfig [] []

parseModule :: String -> DynFlags -> String -> ParseResult (Located (HsModule GhcPs))
parseModule filename flags str =
  unP Parser.parseModule parseState
  where
    location = mkRealSrcLoc (mkFastString filename) 1 1
    buffer = stringToStringBuffer str
    parseState = mkPState flags buffer location

parsePragmasIntoDynFlags :: DynFlags -> FilePath -> String -> IO (Maybe DynFlags)
parsePragmasIntoDynFlags flags filepath str = 
   catchErrors $ do
    let opts = getOptions flags (stringToStringBuffer str) filepath
    (flags, _, _) <- parseDynamicFilePragma flags opts
    return $ Just flags
  where
    catchErrors :: IO (Maybe DynFlags) -> IO (Maybe DynFlags)
    catchErrors act = handleGhcException reportErr
                        (handleSourceError reportErr act)
    reportErr e = do putStrLn $ "error : " ++ show e; return Nothing 

main :: IO ()
main = do

    args <- getArgs
    env <- getEnv "PWD"

    case args of 
      ("--help":_) -> do --They have asked for help
        putStrLn "To launch load a .hs file, i.e `stupid-computer examples/sumpattern.hs`"
        putStrLn "Then expressions can be evaluated via user input, i.e `sum [1..5]`"
        putStrLn "Example files are available in examples/ in the source repo at: "
        putStrLn "https://github.com/alexanderwasey/stupid-computer"
        putStrLn "Such an input file may look like:"
        putStrLn ""
        putStrLn "sum :: Num a => [a] -> a"
        putStrLn "sum (x:xs) = x + sum xs"
        putStrLn "sum [] = 0"
      (x:_) -> do  
        let filename = if (head x == '/') then x else env ++ "/" ++ x
        run filename x
      [] -> do 
        putStrLn "Error : No File Given" 

run :: String -> String -> IO()
run file filename = do 
    s <- readFile' file
    (Just flags) <-
        parsePragmasIntoDynFlags
        (defaultDynFlags fakeSettings fakeLlvmConfig) file s
    case parseModule file (flags `gopt_set` Opt_KeepRawTokenStream) s of
        PFailed s -> do
            let errors = map showSDocUnsafe (pprErrMsgBagWithLoc $ snd (getMessages s flags))
            mapM_ putStrLn errors

        POk s (L _ modu) -> do
          let preppedModule = PrepStage.prepModule modu
          runloop preppedModule flags filename

runloop :: ScTypes.ModuleInfo ->  DynFlags -> String -> IO() 
runloop preppedModule flags filename = do 
  putStrLn $ "Enviroment = " ++ filename

  input <- getLine 

  if (take 2 ((map toLower) input) == ":q")
    then return () 
    else do 
      
      case parseModule "userinput" (flags `gopt_set` Opt_KeepRawTokenStream) input of
        --Users input cannot parse 
        PFailed s -> do 
          let errors = map showSDocUnsafe (pprErrMsgBagWithLoc $ snd (getMessages s flags))
          mapM_ putStrLn errors

        --Parses correctly
        POk s (L _ modu) -> do 
          let toExectute = Tools.getToExecute modu 
          wellTyped <- checkType toExectute preppedModule
          case wellTyped of 
              (True,result) -> do
                let initline = (showSDocUnsafe $ ppr toExectute)
                putStrLn $ "      " ++ initline
                EvalStage.execute toExectute preppedModule initline
                putStrLn "" 
              _ -> do 
                putStrLn $ "Your code will not run, try checking it in GHCi!"

      runloop preppedModule flags filename