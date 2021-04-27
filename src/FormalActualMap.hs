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
import Data.Maybe

matchPatterns :: [HsExpr GhcPs] -> [LPat GhcPs] -> (ScTypes.ModuleInfo) ->  IO(Maybe (Map.Map String (HsExpr GhcPs)))
matchPatterns exprs patterns modu = do 
    maps <- mapM (\(expr,pattern) -> matchPattern expr pattern modu) (zip exprs patterns)

    return $ (Just Map.fromList) <*> (conMaybes maps)

--Now deal with each of the cases for the patterns 

--Simple case with just a variable pattern
matchPattern :: (HsExpr GhcPs) -> (LPat GhcPs) -> (ScTypes.ModuleInfo) -> IO(Maybe ([(String, (HsExpr GhcPs))]))
matchPattern expr (L _ (VarPat _ id)) _ = do return $ Just [(showSDocUnsafe $ ppr id, expr)]

matchPattern (HsPar _ (L _ expr)) (L _ (ParPat _ pat)) modu = matchPattern expr pat modu

matchPattern expr (L _ (ParPat _ pat)) modu = matchPattern expr pat modu

--Currently only concatanation
matchPattern (ExplicitList xep syn (expr:exprs)) (L _(ConPatIn op (InfixCon l r))) modu = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            headmap <- matchPatternL expr l modu 

            let taillist = (ExplicitList xep syn exprs)

            tailmap <- matchPattern taillist r modu

            return $ (++) <$> headmap <*> tailmap

        _ -> do 
            error "Unsupported ConPatIn found"


--When a constructor has just one component
matchPattern (HsApp xep lhs rhs ) (L l (ConPatIn op (PrefixCon ([arg])))) modu = do 
    let lhsstring = showSDocUnsafe $ ppr lhs 
    let opstring = showSDocUnsafe $ ppr op 

    if (lhsstring == opstring) 
        then matchPatternL rhs arg modu 
        else return Nothing 

--When it has more than one 
matchPattern (HsApp xep lhs rhs ) (L l (ConPatIn op (PrefixCon args))) modu = do 
    innermatch <- matchPatternL lhs (L l (ConPatIn op (PrefixCon (init args)))) modu 
    outermatch <- matchPatternL rhs (last args) modu 
    return $ (++) <$> innermatch <*> outermatch 

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
                        _ -> return Nothing
                    return $ (++) <$> headmap <*> tailmap

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
                                    return Nothing
                                            
                        _ -> 
                            return Nothing

                    return $ (++) <$> headmap <*> tailmap
                
                _ -> do 
                    return Nothing 
        _ -> do 
            return Nothing


--Currently only empty list
matchPattern _ (L _ (ConPatIn op (PrefixCon _ ))) _ = do 
    case (showSDocUnsafe $ ppr op) of 
        "[]" -> return (Just [])
        _ -> do 
            return Nothing

matchPattern (ExplicitTuple _ contents _) (L _ (TuplePat _ pats _)) modu = do 
    let matches = [(con, pat) | ((L _ (Present _ con)), pat) <- zip contents pats ]

    maps <- mapM (\(expr,pattern) -> matchPatternL expr pattern modu) matches

    return $ conMaybes maps

matchPattern (ExplicitList _ _ exprs) (L _ (ListPat _ pats)) modu = do 
    maps <- mapM (\(expr,pattern) -> matchPatternL expr pattern modu) (zip exprs pats)

    return $ conMaybes maps

matchPattern _ (L _ (WildPat _)) _ = return $ Just []

matchPattern expr (L _ pat@(NPat _ _ _ _)) _ = do 
    let exprstring = showSDocUnsafe $ ppr expr 
    let patstring = showSDocUnsafe $ ppr pat 
    if (patstring == exprstring) 
        then return (Just [])
        else return Nothing

matchPattern expr (L _ (AsPat _ id pat)) modu = do 
    let leftmap = Just [(showSDocUnsafe $ ppr id, expr)]

    rightmap <- matchPattern expr pat modu 

    return $ (++) <$> leftmap <*> rightmap


matchPattern _ _ _ = return Nothing


--For when has located expressions
matchPatternsL :: [LHsExpr GhcPs] -> [LPat GhcPs] -> (ScTypes.ModuleInfo) ->  IO(Maybe (Map.Map String (HsExpr GhcPs)))
matchPatternsL exprs patterns modu = do 
    let exprs' = map (\(L _ expr) -> expr) exprs 
    matchPatterns exprs' patterns modu 

--Single located expression
matchPatternL :: (LHsExpr GhcPs) -> (LPat GhcPs) -> (ScTypes.ModuleInfo) -> IO(Maybe ([(String, (HsExpr GhcPs))]))
matchPatternL (L _ expr) pattern modu = matchPattern expr pattern modu

conMaybes :: [Maybe [a]] -> Maybe [a]
conMaybes [] = Just []
conMaybes (Nothing:_) = Nothing 
conMaybes (x:xs) = (++) <$> x <*> (conMaybes xs)