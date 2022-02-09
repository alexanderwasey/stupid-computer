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
matchPattern expr (L _ (VarPat _ id)) _ = return $ Just [(showSDocUnsafe $ ppr id, expr)]

matchPattern (HsPar _ (L _ expr)) (L _ (ParPat _ pat)) modu = matchPattern expr pat modu

matchPattern (HsPar _ (L _ expr)) pat modu = matchPattern expr pat modu

matchPattern expr (L _ (ParPat _ pat)) modu = matchPattern expr pat modu

--Currently only concatenation
matchPattern (ExplicitList xep syn (expr:exprs)) (L _(ConPatIn op (InfixCon l r))) modu = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            headmap <- matchPatternL expr l modu 

            let taillist = (ExplicitList xep syn exprs)

            tailmap <- matchPattern taillist r modu

            return $ (++) <$> headmap <*> tailmap

        _ -> do 
            error "Unsupported ConPatIn found"

matchPattern (OpApp xop lhs oper rhs) pat@(L _(ConPatIn op (InfixCon l r))) modu = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            case (showSDocUnsafe $ ppr $ Tools.removeLPars oper) of 
                "(:)" -> do 
                    headmap <- matchPatternL lhs l modu 
                    tailmap <- matchPatternL rhs r modu 
                    return $ (++) <$> headmap <*> tailmap
                "(++)" -> do -- lhs might be empty, and still have a match.
                    --The lhs *should* be an explicit list with one element.
                    case lhs of 
                        (L _ (HsPar _ lhs')) -> matchPattern (OpApp xop lhs' oper rhs) pat modu
                        (L _ (ExplicitList _ _ [lhselem])) -> do 
                            headmap <- matchPatternL lhselem l modu 
                            tailmap <- matchPatternL rhs r modu
                            return $ (++) <$> headmap <*> tailmap 
                        (L _ (ExplicitList _ _ [])) -> matchPatternL rhs pat modu --Check in the rhs for non-empty lists
                        _ -> return Nothing
                _ -> return Nothing

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
    if (null args) then return Nothing
    else do
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

matchPattern _ (L _ (WildPat _)) _ = return $ Just [] -- Matches against `_`

matchPattern expr (L _ pat@(NPat _ _ _ _)) _ = do 
    let exprstr = showSDocUnsafe $ ppr expr
    let patstr = showSDocUnsafe $ ppr pat

    if (exprstr == patstr) 
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

splitList :: (LHsExpr GhcPs) -> (ScTypes.ModuleInfo) -> IO (Maybe (LHsExpr GhcPs, LHsExpr GhcPs))

splitList (L l (ExplicitList xep syn (expr:exprs))) _ = return $ Just (expr, (L l (ExplicitList xep syn exprs)))

splitList (L l (ArithSeq xarith synexp seqInfo)) _ = do 
    case seqInfo of 
        (From expr) -> do 
            let head = expr
            tail <- case expr of 
                (L _ (HsOverLit ext (OverLit extlit (HsIntegral (IL text neg val)) witness))) -> do 
                    let newseq = (ArithSeq xarith synexp (From (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL (SourceText (show $ val+1)) neg (val+1))) witness)))))
                    return newseq
            return $ Just (head, (L l tail))

        (FromTo from to) -> do 
            let head = from

            tail <- case from of 
                (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL text neg val)) witness))) -> do 
                    case to of 
                        (L _ (HsOverLit _ (OverLit _ (HsIntegral (IL _ _ toval)) _))) -> do 
                            let newval = val+1
                            let newlit = (L l (HsOverLit ext (OverLit extlit (HsIntegral (IL (SourceText (show $ newval)) neg (newval))) witness)))
                            
                            let newseq = (ArithSeq xarith synexp (From newlit))
                            
                            if (newval == toval) then 
                                return $ Just (ExplicitList NoExtField Nothing [newlit])
                            else 
                                return $ Just (ArithSeq xarith synexp (FromTo newlit to))
                        _ -> return Nothing
            case tail of 
                (Just t) -> return $ Just (head , (L l t))
                _ -> return Nothing
        _ -> do 
            return Nothing 

splitList (L _ (OpApp _ lhs oper rhs)) _ = do 
    case (showSDocUnsafe $ ppr $ Tools.removeLPars oper) of 
        "(:)" -> do 
            return $ Just (lhs, rhs)
        _ -> return Nothing

splitList (L _ (HsPar _ expr)) modu = splitList expr modu 


splitList _ _ = return Nothing

couldAllMatch :: [(HsExpr GhcPs)] -> [(LPat GhcPs)] -> IO(Bool)
couldAllMatch exprs pats = and <$> mapM (uncurry couldMatch) (zip exprs pats)

couldMatch :: (HsExpr GhcPs) -> (LPat GhcPs) -> IO(Bool)
couldMatch expr (L _ (VarPat _ _)) = return True
couldMatch (HsPar _ (L _ expr)) (L _ (ParPat _ pat)) = couldMatch expr pat
couldMatch (HsPar _ (L _ expr)) pat = couldMatch expr pat
couldMatch expr (L _ (ParPat _ pat)) = couldMatch expr pat
couldMatch (ExplicitList xep syn (expr:exprs)) (L _(ConPatIn op (InfixCon l r))) = do
    case (showSDocUnsafe $ ppr op) of
        ":" -> do
            let headexpr = (\(L _ x) -> x) expr
            lhs <- couldMatch headexpr l
            
            let taillist = (ExplicitList xep syn exprs)
            rhs <- couldMatch taillist r

            return $ lhs && rhs

        _ -> do 
            error "Unsupported ConPatIn found" 
couldMatch (ExplicitList xep syn []) (L _(ConPatIn op (InfixCon l r))) = do
    case (showSDocUnsafe $ ppr op) of
        ":" -> return False
        _ -> do 
            error "Unsupported ConPatIn found" 
couldMatch (ExplicitList _ _ exprs) (L _ (ListPat _ pats)) = do 
    if ((length exprs) /= (length pats)) 
        then return False 
        else do 
            results <- mapM (\((L _ expr),pattern) -> couldMatch expr pattern) (zip exprs pats)
            return $ and results

couldMatch (ExplicitList _ _ _) _ = do
    return False

couldMatch (OpApp xop (L _ lhs) oper (L _ rhs)) pat@(L _(ConPatIn op (InfixCon l r))) = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            case (showSDocUnsafe $ ppr $ Tools.removeLPars oper) of 
                "(:)" -> do 
                    headresult <- couldMatch lhs l  
                    tailresult <- couldMatch rhs r  
                    return $ headresult && tailresult
                "(++)" -> do -- lhs might be empty, and still have a match.
                    --The lhs *should* be an explicit list with one element.
                    case lhs of 
                        (HsPar _ lhs') -> couldMatch (OpApp xop lhs' oper (noLoc rhs)) pat 
                        (ExplicitList _ _ [(L _ lhselem)]) -> do 
                            headresult <- couldMatch lhselem l 
                            tailresult <- couldMatch rhs r 
                            return $ headresult && tailresult
                        (ExplicitList _ _ []) -> couldMatch rhs pat --Check in the rhs for non-empty lists
                        _ -> return False
                _ -> return False

        _ -> do 
            error "Unsupported ConPatIn found"
--When a constructor has just one component
couldMatch (HsApp xep (L _ lhs) (L _ rhs) ) (L l (ConPatIn op (PrefixCon ([arg])))) = do 
    let lhsstring = showSDocUnsafe $ ppr lhs 
    let opstring = showSDocUnsafe $ ppr op 

    if (lhsstring == opstring) 
        then couldMatch rhs arg 
        else return False
--When it has more than one 
couldMatch (HsApp xep (L _ lhs) (L _ rhs) ) (L l (ConPatIn op (PrefixCon args))) = do 
    if (null args) then return False
    else do
        innermatch <- couldMatch lhs (L l (ConPatIn op (PrefixCon (init args))))
        outermatch <- couldMatch rhs (last args)
        return $ innermatch && outermatch 
couldMatch (ArithSeq xarith synexp seqInfo) (L _(ConPatIn op (InfixCon l r))) = do 
    case (showSDocUnsafe $ ppr op) of 
        ":" -> do 
            case seqInfo of 
                (From (L _ expr)) -> do 
                    headmap <- couldMatch expr l 
                    tailmap <- case expr of 
                        (HsOverLit ext (OverLit extlit (HsIntegral (IL text neg val)) witness)) -> do 
                            let newseq = (ArithSeq xarith synexp (From (noLoc (HsOverLit ext (OverLit extlit (HsIntegral (IL (SourceText (show $ val+1)) neg (val+1))) witness)))))
                            couldMatch newseq r 
                        _ -> return False
                    return $ headmap && tailmap

                (FromTo (L _ from) (L _ to)) -> do 
                    headmap <- couldMatch from l 

                    tailmap <- case from of 
                        (HsOverLit ext (OverLit extlit (HsIntegral (IL text neg val)) witness)) -> do 
                            case to of 
                                (HsOverLit _ (OverLit _ (HsIntegral (IL _ _ toval)) _)) -> do 
                                    let newval = val+1
                                    let newlit = (noLoc (HsOverLit ext (OverLit extlit (HsIntegral (IL (SourceText (show $ newval)) neg (newval))) witness))) :: (LHsExpr GhcPs)
                                    
                                    let newseq = (ArithSeq xarith synexp (From newlit))
                                    
                                    if (newval == toval) then 
                                        couldMatch (ExplicitList NoExtField Nothing [newlit]) r  
                                    else 
                                        couldMatch (ArithSeq xarith synexp (FromTo newlit (noLoc to))) r 
                                _ -> 
                                    return False
                                            
                        _ -> 
                            return False

                    return $ headmap && tailmap
                
                _ -> do 
                    return False 
        _ -> do 
            return False
--Currently only empty list
couldMatch _ (L _ (ConPatIn op (PrefixCon _ ))) = do 
    case (showSDocUnsafe $ ppr op) of 
        "[]" -> return True
        _ -> do 
            return False
couldMatch (ExplicitTuple _ contents _) (L _ (TuplePat _ pats _)) = do 
    if ((length contents) /= (length pats)) 
        then return False
        else do
            let matches = [(con, pat) | ((L _ (Present _ con)), pat) <- zip contents pats ]

            maps <- mapM (\((L _ expr),pattern) -> couldMatch expr pattern) matches

            return $ and maps

couldMatch _ (L _ (WildPat _)) = return True
--When matching against a literal
couldMatch expr@(HsOverLit _ _) (L _ pat@(NPat _ _ _ _)) = do
    let exprstr = showSDocUnsafe $ ppr expr
    let patstr = showSDocUnsafe $ ppr pat

    return (exprstr == patstr) 
couldMatch expr@(HsLit _ _) (L _ pat@(NPat _ _ _ _)) = do
    let exprstr = showSDocUnsafe $ ppr expr
    let patstr = showSDocUnsafe $ ppr pat

    return (exprstr == patstr) 
couldMatch _ (L _ (NPat _ _ _ _)) = return True
couldMatch expr (L _ (AsPat _ _ pat)) = couldMatch expr pat
couldMatch expr@(HsVar _ _) pat = return ((showSDocUnsafe $ ppr expr) == (showSDocUnsafe $ ppr pat))
couldMatch exp _ = return True