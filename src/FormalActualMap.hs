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

matchPatterns :: [HsExpr GhcPs] -> [LPat GhcPs] -> (ScTypes.ModuleInfo) ->  IO(Map.Map String (HsExpr GhcPs))
matchPatterns exprs patterns modu = do 
    maps <- mapM (\(expr,pattern) -> matchPattern expr pattern modu) (zip exprs patterns)

    return $ Map.fromList (concat maps)


--Now deal with each of the cases for the patterns 

--Simple case with just a variable pattern
matchPattern :: (HsExpr GhcPs) -> (LPat GhcPs) -> (ScTypes.ModuleInfo) -> IO([(String, (HsExpr GhcPs))])
matchPattern expr (L _ (VarPat _ id)) _ = do return [(showSDocUnsafe $ ppr id, expr)]

matchPattern expr (L _ (ParPat _ pat)) modu = do
    matchPattern expr pat modu

--Currently only concatanation
matchPattern (ExplicitList xep syn (expr:exprs)) (L _(ConPatIn op (InfixCon l r))) modu = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            headmap <- matchPatternL expr l modu 

            let taillist = (ExplicitList xep syn exprs)

            tailmap <- matchPattern taillist r modu

            return (headmap ++ tailmap)

        _ -> do 
            error "Unsupported ConPatIn found"

matchPattern (ArithSeq xarith synexp seqInfo) (L _(ConPatIn op (InfixCon l r))) modu = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            case seqInfo of 
                (From expr) -> do 
                    headmap <- matchPatternL expr l modu
                    tailmap <- case expr of 
                        (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL text neg val)) witness))) -> do 
                            let newseq = (ArithSeq xarith synexp (From (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL (SourceText (show $ val+1)) neg (val+1))) witness)))))
                            matchPattern newseq r modu
                        _ -> 
                            error "Unsupported ArithSeq conrtents"
                    return (headmap ++ tailmap)

                (FromTo from to) -> do 
                    headmap <- matchPatternL from l modu 

                    tailmap <- case from of 
                        (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL text neg val)) witness))) -> do 
                            case to of 
                                (L _ (HsOverLit _ (OverLit _ (HsIntegral (IL _ _ toval)) _))) -> do 
                                    let newval = val+1
                                    let newlit = (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL (SourceText (show $ newval)) neg (newval))) witness)))
                                    
                                    let newseq = (ArithSeq xarith synexp (From newlit))
                                    
                                    if (newval == toval) then 
                                        matchPattern (ExplicitList NoExtField Nothing [newlit]) r modu 
                                    else 
                                        matchPattern (ArithSeq xarith synexp (FromTo newlit to)) r modu
                                _ -> 
                                    error "Unsupported ArithSeq conrtents" 
                                            
                        _ -> 
                            error "Unsupported ArithSeq conrtents"

                    return (headmap ++ tailmap)
                
                _ -> do 
                    error "Unsupported type of arithmetic list"
        _ -> do 
            error "Unsupported ConPatIn found"


--Currently only empty list
matchPattern _ (L _ (ConPatIn op (PrefixCon _ ))) _ = do 
    case (showSDocUnsafe $ ppr op) of 
        "[]" -> return [] 
        _ -> do 
            error "Unsupported ConPatIn found - PrefixCon"



matchPattern _ pat modu = do 
    error $ showSDocUnsafe $ ppr pat 







--For when has located expressions
matchPatternsL :: [LHsExpr GhcPs] -> [LPat GhcPs] -> (ScTypes.ModuleInfo) ->  IO(Map.Map String (HsExpr GhcPs))
matchPatternsL exprs patterns modu = do 
    let exprs' = map (\(L _ expr) -> expr) exprs 
    matchPatterns exprs' patterns modu 

--Single located expression
matchPatternL :: (LHsExpr GhcPs) -> (LPat GhcPs) -> (ScTypes.ModuleInfo) -> IO([(String, (HsExpr GhcPs))])
matchPatternL (L _ expr) pattern modu = matchPattern expr pattern modu