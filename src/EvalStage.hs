{-# LANGUAGE PackageImports, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module EvalStage where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" DynFlags
import "ghc-lib-parser" GHC.Hs.Binds
import "ghc-lib-parser" BasicTypes
import "ghc-lib-parser" TcEvidence


import qualified Data.Map.Strict as Map
import Data.List
import Data.Either
import Data.Char
import Data.Maybe
import Bag
import Control.Monad
import Control.Monad.State

import Tools 
import ScTypes
import FormalActualMap
import DefinitionGetter
import NormalFormReducer 
import PrepStage


--The Integer is how many variables are bound to the Found function
--The String is the name of the function 
data TraverseResult = Reduced | NotFound | Found Integer String | Constructor deriving (Eq)

--Execute the computation fully
execute :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> String -> DynFlags -> StateT ScTypes.EvalState IO(LHsDecl GhcPs)
execute decl funMap prevline flags = do 
  (newdecl, changed) <- EvalStage.evalDecl decl funMap flags
  case changed of 
      Reduced -> do 
        let newline = (showSDocUnsafe $ ppr newdecl)
        
        if (newline /= prevline) then do
            let newlines = lines newline 
            liftIO $ putStrLn $ "   =  " ++ (head newlines)

            liftIO $ mapM_ (\x -> putStrLn ("      " ++ x)) (tail newlines) --Print the other lines


            else do 
                return ()
        execute newdecl funMap newline flags 
      _ -> do
        return $ decl

--Do one stage of evaluation on the Decl -- Has to be IO as we make calls to GHCi
evalDecl :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> DynFlags -> StateT ScTypes.EvalState IO(LHsDecl GhcPs, TraverseResult)
evalDecl (L l(SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr)) g ))) modu flags = do 
    (expr', result) <- evalExpr expr modu Map.empty flags
    let decl' = (L l (SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr')) g ))) --Return our declaration to the correct context
    return (decl', result)
evalDecl _ _ _ = error "Should be evaluating SpliceD"

--Evaluating an expression
-- Will be evaluating the LHS of any expression first, so only one will be expanded at a time
--Each case will be a bit different
evalExpr :: (LHsExpr GhcPs) -> ScTypes.ModuleInfo -> ScTypes.ModuleInfo -> DynFlags -> StateT ScTypes.EvalState IO(LHsExpr GhcPs, TraverseResult)

--Found a variable, if it is one of our functions, return we have found it
--If it is one of our varibles then do a substitution for the value
evalExpr var@(L l (HsVar xVar id)) funcMap hidden flags = do
    let name = showSDocUnsafe $ ppr id 

    if (isUpper $ head $ name)
        then return (var, Constructor)
    else
        if (Map.member name funcMap)
            then do 
                let n = numargs (funcMap Map.! name )
                if (n == 0) 
                    then evalApp (L l (HsVar xVar id)) funcMap hidden flags
                    else return ((L l (HsVar xVar id)), Found 0 name) --This is a function which requires more arguments
            else do 
                return (var, NotFound)     

--Applicaton statement 
evalExpr application@(L l (HsApp xApp lhs rhs)) funcMap hidden flags = do 
    (lhs' , lhsresult) <- evalExpr lhs funcMap hidden flags --Traverse the lhs
    (rhs' , rhsresult) <- evalExpr rhs funcMap hidden flags-- Traverse the rhs
    case lhsresult of 
        (Found i name) -> do 
            argsNeeded <- case (funcMap Map.!? name) of 
                (Just funcinfo)  -> return (numargs funcinfo)
                _ -> error $ Tools.errorMessage ++ name ++ " not found in funcMap - evalExpr" 

            if (argsNeeded == (i + 1)) -- +1 because including the argument in the rhs of this application
                then evalApp application funcMap hidden flags
            else return (application, (Found (i+1) name)) --Go up a level and try and find more argument

        NotFound -> do --In this case explore the rhs
            case rhsresult of 
                Reduced -> do 
                    let newApp = (L l (HsApp xApp lhs (removeLPars rhs')))
                    return (newApp, rhsresult)
                -- Attempt to evaluate
                _ -> do 
                    collapsed <- lift $ NormalFormReducer.reduceNormalForm application flags 

                    case collapsed of 
                        Nothing -> return (application, NotFound)
                        (Just expr) -> return (expr, Reduced)
        
        Constructor -> do --In this case a constructor.
            case rhsresult of
                Reduced -> do 
                    let newApp = (L l (HsApp xApp lhs (removeLPars rhs')))
                    return (newApp, Reduced)
                _ -> 
                    return (application, Constructor)

        _ -> return ((L l (HsApp xApp lhs' rhs)), lhsresult)

evalExpr application@(L l (OpApp xop lhs op rhs)) funcMap hidden flags = do 
    (op', opresult) <- evalExpr op funcMap hidden flags -- Try and reduce the op.

    case opresult of 
        Reduced -> return ((L l (OpApp xop lhs op' rhs)), Reduced)
        _ -> do 
            (lhs' , lhsresult) <- evalExpr lhs funcMap hidden flags--Traverse the lhs
        
            let thisApp = (L l (OpApp xop lhs' op rhs))
            
            (hsapp, found) <- case lhsresult of 
                Reduced -> return (thisApp, Reduced) 
                _ -> do 
                    (rhs', rhsresult) <- evalExpr rhs funcMap hidden flags --Traverse rhs 
                    case rhsresult of 
                        Reduced -> do
                            return (L l (OpApp xop lhs' op rhs'), rhsresult)
                        _ -> do
                            let funname = showSDocUnsafe $ ppr $ op

                            if (Map.member funname funcMap)
                                then evalApp (L l (HsApp NoExtField (L l (HsApp NoExtField op lhs)) rhs)) funcMap hidden flags --Treat it as a prefix operation
                                else do
                                    reduced <- lift $ NormalFormReducer.reduceNormalForm application flags 
                                    case reduced of 
                                        Nothing -> return (application, NotFound)
                                        (Just normal) -> return (normal, Reduced)
                    
            return (hsapp, found)

--Deal with parentheses 
evalExpr (L l (HsPar xpar expr)) funcMap hidden flags = do 
    (expr', found) <- evalExpr expr funcMap hidden flags 
    return ((L l (Tools.removePars (HsPar xpar expr'))), found)

--Deal with if/else statement
evalExpr orig@(L l (HsIf xif syn cond lhs rhs)) funcMap hidden flags = do 

    let condstr = showSDocUnsafe $ ppr $ Tools.removeLPars cond 

    case condstr of 
        "True" -> return (lhs, Reduced) 
        "False" -> return (rhs, Reduced) 
        _ -> do 
            (cond' , replaced) <- evalExpr cond funcMap hidden flags

            case replaced of 
                Reduced -> return ((L l (HsIf xif syn cond' lhs rhs)), Reduced)
                _ -> do 
                    collapsed <- lift $ NormalFormReducer.reduceNormalForm cond flags 
                    case collapsed of 
                        (Just cond'') -> return ((L l (HsIf xif syn cond'' lhs rhs)), Reduced) 
                        _ -> return (orig, NotFound)
                        
--Deal with lists
evalExpr (L l (ExplicitList xep msyn (expr:exprs))) funcMap hidden flags = do 
    (expr' , replaced) <- evalExpr expr funcMap hidden flags 

    case replaced of 
        Reduced -> return  ((L l (ExplicitList xep msyn (expr':exprs))), Reduced)

        _ -> do 
            ((L l (ExplicitList _ _ exprs')), replaced') <- evalExpr (L l (ExplicitList xep msyn exprs)) funcMap hidden flags 
            return ((L l (ExplicitList xep msyn (expr:exprs'))), replaced')

evalExpr (L l (ExplicitList xep msyn [])) _ _ _ = do 
    return ((L l (ExplicitList xep msyn [])), NotFound)

--Deal with tuples
evalExpr (L l (ExplicitTuple xtup (expr:exprs) box)) funcMap hidden flags = do 
    case expr of 
        (L l' (Present xpres tupexp)) -> do  
            (expr' , replaced) <- evalExpr tupexp funcMap hidden flags 
            case replaced   of 
                Reduced -> do 
                    let tuple = (L l' (Present xpres expr'))
                    return  ((L l (ExplicitTuple xtup (tuple:exprs) box)), Reduced)

                _ -> do 
                    ((L l (ExplicitTuple _ exprs' _)), replaced') <- evalExpr (L l (ExplicitTuple xtup exprs box)) funcMap hidden flags 
                    return ((L l (ExplicitTuple xtup (expr:exprs') box)), replaced')
        
        _ -> do 
            ((L l (ExplicitTuple _ exprs' _)), replaced') <- evalExpr (L l (ExplicitTuple xtup exprs box)) funcMap hidden flags 
            return ((L l (ExplicitTuple xtup (expr:exprs') box)), replaced')

evalExpr (L l (ExplicitTuple xtup [] box)) _ _ _ = do 
    return ((L l (ExplicitTuple xtup [] box)), NotFound)

--List comprehensions
evalExpr comp@(L l (HsDo xDo ListComp (L l' (stmt: stmts)))) funcMap hidden flags = do 
    case stmt of 
        
        -- Try and pattern match (x:xs) against it. If this fails then attempt to expand it. 
        -- Need to work out if it is empty? 
        -- Utilise the definition getter for this work. 
        
        (L l (BindStmt a pat lexpr@(L _ expr) e f)) -> do 
            
            exprNotEmpty <- lift $ matchesPattern expr "(x:xs)" funcMap
            
            if (not exprNotEmpty) then 
                -- Returns an empty list.
                return ((L l (ExplicitList NoExtField Nothing [])), Reduced)
            else do 
                maybehead <- lift $ FormalActualMap.splitList lexpr funcMap
                case maybehead of 
                    Nothing -> do 
                        (newexpr, res) <- evalExpr lexpr funcMap hidden flags 
                        let newstmt = (L l (BindStmt a pat newexpr e f))
                        let newcomp = ((L l (HsDo xDo ListComp (L l' (newstmt: stmts)))))
                        return (newcomp, res)
                    
                    Just (headexpr, tailexpr) -> do 
                        let newcomp = (HsDo xDo ListComp (L l' stmts))
                        map <- lift $ FormalActualMap.matchPatternL headexpr pat funcMap

                        lhs <- case map of 
                            Nothing -> 
                                return (L l (ExplicitList NoExtField Nothing []))
                            Just m -> do
                                -- Create the new lists. 
                                let newlistcomps = (\v -> (L l (subValues newcomp v))) (Map.fromList m)
                                return $ listCompFinished newlistcomps

                        case (showSDocUnsafe $ ppr tailexpr) of 
                            "[]" -> 
                                return (lhs, Reduced)
                            _ -> do 
                                let newstmts = (L l (BindStmt a pat tailexpr e f)) : stmts 

                                let finalexpr = combineLists [lhs, (L l (HsDo xDo ListComp (L l' newstmts)))]

                                return (finalexpr, Reduced)

        (L l (BodyStmt ext condition lexpr rexpr)) -> do
            (condition', replaced) <- evalExpr condition funcMap hidden flags --Evaluate the condition

            case replaced of 
                Reduced -> do 
                    let newcond = (L l (BodyStmt ext condition' lexpr rexpr))
                    let newcomp = (L l (HsDo xDo ListComp (L l' (newcond: stmts))))
                    return (newcomp, Reduced)
                _ -> do 
                    let condstring = showSDocUnsafe $ ppr condition'
                    if condstring == "True" 
                        then do
                            case stmts of 
                                [(L l (LastStmt _ body _ _))] -> do
                                    return ((L l (ExplicitList NoExtField Nothing [body])), Reduced)
                                _ -> do 
                                    let newcomp = (L l (HsDo xDo ListComp (L l' stmts)))
                                    return (newcomp, Reduced)
                        else 
                            return ((L l (ExplicitList NoExtField Nothing [])), Reduced)
        (L l (LastStmt _ body _ _)) -> do --If only has a body left
            return ((L l (ExplicitList NoExtField Nothing [body])), NotFound)
        _ -> do
            return (comp, NotFound)

-- Let expressions - currently doesn't support pattern matching in the bind.
evalExpr letexpr@(L l (HsLet xlet (L _ localbinds) lexpr@(L _ expr))) funcMap hidden flags = do 

    case localbinds of 
        HsValBinds a (ValBinds b bag c) -> do --Add the fully reduced expressions to the context

            let expressions = bagToList bag 

            let defs = map PrepStage.prepBind expressions

            let names = map (\x -> head $ Map.keys x) defs
            let counts = countArgs (Map.fromList $ zip names (repeat 0)) expr

            if (sum $ Map.elems counts) == 0 then return (lexpr, Reduced)
            else do 
                --Remove keys from map which are defined in this let binding
                let funcMap' = foldr Map.delete funcMap (concatMap Map.keys defs) 
                let hidden' = foldr Map.delete hidden (concatMap Map.keys defs)

                fullyReducedDefs <- lift $ filterM (\x -> fullyReduced (noLoc $ getDefFromBind x) funcMap hidden flags) expressions
                nonFullyReducedDefs <- lift $ filterM (\x -> not <$> fullyReduced (noLoc $ getDefFromBind x) funcMap hidden flags) expressions


                let newDefs = map PrepStage.prepBind fullyReducedDefs
                let newHiddenDefs = map PrepStage.prepBind nonFullyReducedDefs
                
                let newDefsUnions = Map.union funcMap' (Map.unions newDefs)
                let newHiddenDefsUnions = Map.union hidden' (Map.unions newHiddenDefs)

                (lexpr', result) <- evalExpr lexpr newDefsUnions newHiddenDefsUnions flags

                case result of 
                        Reduced -> return ((L l (HsLet xlet (L l localbinds) lexpr')), result)
                        _ -> do --Reduce an expression in the let (if possible)
                            (expressions', result') <- evalLetBindings expressions funcMap hidden flags 
                            let bag' = listToBag expressions'
                            let localbinds' = HsValBinds a (ValBinds b bag' c)
                            
                            return ((L l (HsLet xlet (L l localbinds') lexpr)), result')

        _ -> error "Error in let expression"

evalExpr lit@(L l (HsLit xlit hslit)) _ _ _ =  return (lit, NotFound)

evalExpr lit@(L l (HsOverLit xlit hslit)) _ _ _ = return (lit, NotFound)

evalExpr (L l (NegApp xneg expr syn)) funcMap hidden flags = do 
    (newexp, result) <- evalExpr expr funcMap hidden flags   

    return ((L l (NegApp xneg newexp syn)), result)

evalExpr arith@(L l (ArithSeq xarith syn (From from))) funcMap hidden flags = do 
    (from', result) <- evalExpr from funcMap hidden flags
    return (L l (ArithSeq xarith syn (From from')), result)

evalExpr arith@(L l (ArithSeq xarith syn (FromTo from to))) funcMap hidden flags = do 
    (from', result) <- evalExpr from funcMap hidden flags

    case result of 
        Reduced -> return (L l (ArithSeq xarith syn (FromTo from' to)), result)
        _ -> do 
            (to', result') <- evalExpr to funcMap hidden flags
            return (L l (ArithSeq xarith syn (FromTo from to')), result')

evalExpr arith@(L l (ArithSeq xarith syn (FromThen from to))) funcMap hidden flags = do 
    (from', result) <- evalExpr from funcMap hidden flags

    case result of 
        Reduced -> return (L l (ArithSeq xarith syn (FromThen from' to)), result)
        _ -> do 
            (to', result') <- evalExpr to funcMap hidden flags
            return (L l (ArithSeq xarith syn (FromThen from to')), result')

evalExpr arith@(L l (ArithSeq xarith syn (FromThenTo from the to))) funcMap hidden flags = do 
    (from', result) <- evalExpr from funcMap hidden flags

    case result of 
        Reduced -> return (L l (ArithSeq xarith syn (FromThenTo from' the to)), result)
        _ -> do 
            (the', result') <- evalExpr the funcMap hidden flags
            case result' of 
                Reduced -> return (L l (ArithSeq xarith syn (FromThenTo from the' to)), result')
                _ -> do 
                    (to', result'') <- evalExpr to funcMap hidden flags
                    return (L l (ArithSeq xarith syn (FromThenTo from the to')), result'')



evalExpr expr _ _ flags = do --If not defined for then make an attempt to reduce to normal form    
    result <- lift $ NormalFormReducer.reduceNormalForm expr flags
    
    case result of 
        Nothing -> return (expr, NotFound)
        (Just normal) -> return (normal, Reduced)

--Evaluates a function (one step)
--Presumes it is a function applied to the correct number of args
--Currently assumes the function is not within some parenthesis (bad assumption)
evalApp :: (LHsExpr GhcPs) -> ScTypes.ModuleInfo -> ScTypes.ModuleInfo -> DynFlags -> StateT EvalState IO((LHsExpr GhcPs, TraverseResult))
evalApp lexpr@(L l expr@(HsApp xapp lhs rhs)) modu hidden flags = do
        let (func, args) = Tools.getFuncArgs (L l expr) --(head exprs, tail exprs) --Get the expression(s) for the function and the arguments 
        mDef <- lift $ DefinitionGetter.getDef func args (Map.union modu hidden) --Get the appropriate rhs given the arguments 
        case mDef of 
            Just (def, pattern, pats) -> do   
                let patterns = reverse $ Map.elems pats                
                let patstr = showSDocUnsafe $ ppr pattern
                let prevpats = takeWhile (\pat -> (showSDocUnsafe $ ppr pat) /= patstr) patterns
                
                --Need to check if any of the previous patterns could *still* match with the inputs.
                prevmatch <- lift $ mapM (\pat -> FormalActualMap.couldAllMatch args pat) prevpats

                if (or prevmatch) then do 
                    --This gets the other possible patterns for each variable
                    let otherpossiblepatterns = transpose $ map snd $ filter fst (zip prevmatch prevpats)
                    
                    --Tuples of, the input, the proper pattern, and the other possible patterns
                    let varpropother = zip3 args pattern otherpossiblepatterns

                    (newargs,result) <- evalAmbiguousArguments varpropother modu hidden flags
                    
                    return ((applyArgs func newargs), result)
                else do
                    --Get the appropriate formal-actual mapping given the arguments 
                    --But only if none of the other arguments match 
                    valmap <- lift $ FormalActualMap.matchPatterns args pattern modu

                    case valmap of 
                        Nothing -> do 
                            --Try to evaluate the first of the arguments which doesn't pattern match
                            (newargs, result) <- evalNonMatchingArguments (zip args pattern) modu hidden flags
                            return ((applyArgs func newargs), result)

                        (Just vmap) -> do 
                            -- The initial arg counts
                            let argcounts = countArgs (Map.fromList (zip (Map.keys vmap) (repeat 0))) def
                            let repeated = Map.keys $ Map.filter (>1) argcounts

                            --The arguments which need to be bound in a let expression
                            toBind <- lift $ filterM (\x -> fmap not (fullyReduced (noLoc $ vmap Map.! x) modu hidden flags)) repeated
                            
                            --Remove the values which need to be bound
                            let vmap' = foldr Map.delete vmap toBind -- The vmap of expressions that need to be subbed in

                            let expr' = subValues def vmap'--Substitute formals for actuals 

                            --Create a let expression for each bound value
                            expr'' <- foldM (\exp -> (\name -> createLetExpression exp name (vmap Map.! name))) expr' toBind 

                            return (noLoc expr'', Reduced)

            _ -> return (lexpr, NotFound)
evalApp lexpr@(L l expr@(HsVar _ _ )) modu hidden _ = do 
    mdef <- lift $ DefinitionGetter.getDef expr [] modu
    case mdef of 
        Just (def, _, _) -> return ((L l def), Reduced)
        _ -> return (lexpr, NotFound)


subLocatedValue :: (LHsExpr GhcPs) -> (Map.Map String (HsExpr GhcPs)) -> (LHsExpr GhcPs)
subLocatedValue (L l expr) vmap = (L l (subValues expr vmap))

--Substitues actuals into formals
subValues :: (HsExpr GhcPs) -> (Map.Map String (HsExpr GhcPs)) -> (HsExpr GhcPs)
subValues (HsVar xvar (L l id)) vmap = case possSub of 
    Nothing -> (HsVar xvar (L l id)) 
    (Just value) -> value
    where 
        name = occNameString $ rdrNameOcc id 
        possSub = Map.lookup name vmap

subValues (HsApp xapp (L ll lhs) (L rl rhs)) vmap = (HsApp xapp (L ll (subValues lhs vmap)) (L rl (subValues rhs vmap)))
subValues (OpApp xop (L ll l) (L lm m) (L lr r)) vmap = (OpApp xop (L ll (subValues l vmap)) (L lm (subValues m vmap)) (L lr (subValues r vmap)))
subValues (HsPar xpar (L l exp)) vmap = Tools.removePars (HsPar xpar (L l (subValues exp vmap)))
subValues (NegApp xneg (L l exp) synt) vmap = (NegApp xneg (L l (subValues exp vmap)) synt)
subValues (ExplicitTuple xtup elems box) vmap = (ExplicitTuple xtup elems' box) where elems' = map ((flip subValuesTuple) vmap) elems
subValues (ExplicitList xlist syn exprs) vmap = (ExplicitList xlist syn exprs') where exprs' = map (\(L l expr) -> (L l (subValues expr vmap))) exprs
subValues (HsIf xif syn cond lhs rhs) vmap = (HsIf xif syn (subLocatedValue cond vmap) (subLocatedValue lhs vmap) (subLocatedValue rhs vmap))
subValues (HsDo xdo ListComp (L l stmts)) vmap = (HsDo xdo ListComp (L l stmts'))
    where stmts' = map ((flip subValuesLStmts) vmap) stmts
subValues (SectionL xSection (L ll lhs) (L rl rhs)) vmap = (SectionL xSection (L ll (subValues lhs vmap)) (L rl (subValues rhs vmap)))
subValues (SectionR xSection (L ll lhs) (L rl rhs)) vmap = (SectionL xSection (L ll (subValues lhs vmap)) (L rl (subValues rhs vmap)))
subValues (ArithSeq xarith syn seqinfo) vmap = (ArithSeq xarith syn (subValuesArithSeq seqinfo vmap))


subValues expr _ = expr

subValuesTuple :: (LHsTupArg GhcPs) -> (Map.Map String (HsExpr GhcPs)) -> (LHsTupArg GhcPs)
subValuesTuple (L l (Present xpres (L l' expr))) vmap = (L l (Present xpres (L l' expr'))) where expr' = subValues expr vmap 
subValuesTuple (L l tup) vmap = (L l tup)

subValuesLStmts :: (ExprLStmt GhcPs) -> (Map.Map String (HsExpr GhcPs)) -> (ExprLStmt GhcPs)
subValuesLStmts (L l (BindStmt ext pat (L l' body) lexpr rexpr)) vmap = (L l (BindStmt ext pat (L l' body') lexpr rexpr))
    where body' = subValues body vmap
subValuesLStmts (L l (BodyStmt ext (L l' body) lexpr rexpr)) vmap = (L l (BodyStmt ext (L l' body') lexpr rexpr))
    where body' = subValues body vmap
subValuesLStmts (L l (LastStmt ext (L l' body) b expr)) vmap = (L l (LastStmt ext (L l' body') b expr))
    where body' = subValues body vmap

subValuesLStmts stmt _ = stmt

subValuesArithSeq (From (L l expr)) vmap = (From (L l (subValues expr vmap)))
subValuesArithSeq (FromThen (L l lhs) (L _ rhs)) vmap = (FromThen (L l (subValues lhs vmap)) (L l (subValues rhs vmap)))
subValuesArithSeq (FromTo (L l lhs) (L _ rhs)) vmap = (FromTo (L l (subValues lhs vmap)) (L l (subValues rhs vmap)))
subValuesArithSeq (FromThenTo (L l lhs) (L _ mid) (L _ rhs)) vmap = (FromThenTo (L l (subValues lhs vmap)) (L l (subValues mid vmap)) (L l (subValues rhs vmap)))

--Counts the args which appear in the input map in this expression
countArgs :: (Map.Map String Integer) -> (HsExpr GhcPs) -> (Map.Map String Integer)
countArgs m (HsVar xvar (L l id)) = case (Map.lookup name m) of 
    Nothing -> m 
    (Just count) -> Map.insert name (count+1) m
    where
        name = occNameString $ rdrNameOcc id

countArgs m (HsApp _ (L _ lhs) (L _ rhs)) = Map.unionsWith (+) [countArgs m' lhs, countArgs m' rhs, m]
    where m' = emptycountmap m
countArgs m (OpApp _ (L _ lhs) (L _ op) (L _ rhs)) = Map.unionsWith (+) [countArgs m' op, countArgs m' lhs, countArgs m' rhs, m]
    where m' = emptycountmap m
countArgs m (HsPar _ (L _ exp)) = countArgs m exp
countArgs m (NegApp _ (L _ exp) _) = countArgs m exp
countArgs m (ExplicitTuple _ exprs _) = Map.unionsWith (+) (m:[countArgs m' exp | (L _ (Present _ (L _ exp))) <- exprs])
    where m' = emptycountmap m
countArgs m (ExplicitList _ _ exprs) = Map.unionsWith (+) (m:(map (\(L _ exp) -> countArgs m' exp) exprs))
    where m' = emptycountmap m
countArgs m (HsIf _ _ (L _ cond) (L _ lhs) (L _ rhs)) = Map.unionsWith (+) [countArgs m' cond, countArgs m' lhs, countArgs m' rhs, m] 
    where m' = emptycountmap m
countArgs m (HsDo _ ListComp (L _ stmts)) = Map.unionsWith (+) (m:(map (countArgsLStmt m') stmts))
    where m' = emptycountmap m
countArgs m (SectionL _ (L _ lhs) (L _ rhs)) = Map.unionsWith (+) [countArgs m' lhs, countArgs m' rhs, m]
    where m' = emptycountmap m
countArgs m (SectionR _ (L _ lhs) (L _ rhs)) = Map.unionsWith (+) [countArgs m' lhs, countArgs m' rhs, m]
    where m' = emptycountmap m
countArgs m (ArithSeq _ _ seqinfo) = countArgsArithSeq m seqinfo
countArgs m (HsLet _ (L _ (HsValBinds _ (ValBinds _ bag _))) (L _ expr)) = Map.unionsWith (+) ([m, countArgs m' expr] ++ (map (countArgs m) rhss))
    where 
        expressions = bagToList bag
        defs = map PrepStage.prepBind expressions
        names = Map.keys $ Map.unions defs
        rhss = map getDefFromBind expressions
        m' = emptycountmap $ foldr Map.delete m names
countArgs m (HsLet _ _ (L _ expr)) = countArgs m expr 
countArgs m _ = m

countArgsArithSeq m (From (L _ expr)) = countArgs m expr
countArgsArithSeq m (FromThen (L _ lhs) (L _ rhs)) = Map.unionsWith (+) [countArgs m' lhs, countArgs m' rhs, m]
    where m' = emptycountmap m
countArgsArithSeq m (FromTo (L _ lhs) (L _ rhs)) = Map.unionsWith (+) [countArgs m' lhs, countArgs m' rhs, m]
    where m' = emptycountmap m
countArgsArithSeq m (FromThenTo (L _ lhs) (L _ mid) (L _ rhs)) = Map.unionsWith (+) [countArgs m' lhs, countArgs m' rhs, countArgs m' mid, m]
    where m' = emptycountmap m

countArgsLStmt :: (Map.Map String Integer) -> (ExprLStmt GhcPs) -> (Map.Map String Integer)
countArgsLStmt m (L _ (BindStmt _ _ (L _ body) _ _)) = countArgs m body  
countArgsLStmt m (L _ (BodyStmt _ (L _ body) _ _)) = countArgs m body
countArgsLStmt m (L _ (LastStmt _ (L _ body) _ _)) = countArgs m body
countArgsLStmt m _ = m

emptycountmap m = Map.fromList $ zip (Map.keys m) (repeat 0)

getBind :: [ExprLStmt GhcPs] -> (Maybe ((ExprLStmt GhcPs)), [ExprLStmt GhcPs])
getBind (((L l (BindStmt ext pat body lexpr rexpr))):exprs) = ((Just (L l (BindStmt ext pat body lexpr rexpr))), exprs)
getBind (expr:exprs) = (bind, expr:exprs')
    where (bind, exprs') = getBind exprs
getBind [] = (Nothing, [])

getBody :: [ExprLStmt GhcPs] -> (Maybe (LHsExpr GhcPs), [ExprLStmt GhcPs])
getBody (((L l (BodyStmt ext body lexpr rexpr))):exprs) = (Just body, exprs)
getBody (expr:exprs) = (bind, expr:exprs')
    where (bind, exprs') = getBody exprs
getBody [] = (Nothing, [])

--Combines lists together 
combineLists :: [LHsExpr GhcPs] -> (LHsExpr GhcPs)
combineLists [expr] = expr
combineLists (expr:exprs) = noLoc (OpApp NoExtField expr op rhs)
    where rhs = combineLists exprs
          op = noLoc (Tools.stringtoId "++")

--If the list comp is finished, return it as a list, else return it as (the same) list comp 
listCompFinished :: (LHsExpr GhcPs) -> (LHsExpr GhcPs)
listCompFinished (L l (HsDo xDo ListComp (L l' stmts))) = 
    case bind of 
        (Just _) -> (L l (HsDo xDo ListComp (L l' stmts)))   --In this case there are still more expansions to be done 
        _ -> case body of 
                (Just _) -> (L l (HsDo xDo ListComp (L l' stmts))) -- Still have more conditions to deal with
                _ -> (L l (ExplicitList NoExtField Nothing elements)) --Have nothing else to do so just return a list
    where 
        (bind, nonbinds) = getBind stmts
        (body, nonbody) = getBody stmts
        elements = map (\(L l (LastStmt _ body _ _)) -> body) stmts

--Check to see if an expression is fully reduced
fullyReduced :: (LHsExpr GhcPs) -> ScTypes.ModuleInfo -> ScTypes.ModuleInfo -> DynFlags -> IO(Bool)
fullyReduced expr funcMap hidden flags = do
  ((_, result), _) <- runStateT (evalExpr expr funcMap hidden flags) Map.empty
  case result of 
    Reduced -> return False
    _ -> return True 

--Try and reduce the first let binding which can be reduced
evalLetBindings :: [(LHsBindLR GhcPs GhcPs)] -> ScTypes.ModuleInfo -> ScTypes.ModuleInfo -> DynFlags -> StateT EvalState IO([(LHsBindLR GhcPs GhcPs)], TraverseResult)
evalLetBindings [] _ _ _ = return ([], NotFound) -- Base case, nothing to do here
evalLetBindings (orig@(L l (FunBind a b (MG c (L _ ((L _ (Match x y z (GRHSs g ((L _ (GRHS o p expr) ):bodies) h))):defs)) d ) e f)):xs) modu hidden flags = do
    --Check to see if the first can be reduced
    (expr', reduced) <- evalExpr expr modu hidden flags
    case reduced of 
        Reduced -> do 
            let neworig = (L l (FunBind a b (MG c (L l ((L l (Match x y z (GRHSs g ((L l (GRHS o p expr') ):bodies) h))):defs)) d ) e f))
            return ((neworig:xs), Reduced)
        _ -> do --Instead reduce the tail
            (xs', tailreduced) <- evalLetBindings xs modu hidden flags
            return (orig:xs', tailreduced)

--Creates a let expression
--A bit complicated as it has to create an entire function!
createLetExpression :: (HsExpr GhcPs) -> String -> (HsExpr GhcPs) -> StateT EvalState IO(HsExpr GhcPs)
createLetExpression expr varname varvalue = do

        var_numberings <- get

        --The variables `shown` by let expressions will be given numberings
        --This will help users differentiate them
        let var_numbering = case var_numberings Map.!? varname of 
                Nothing -> 0
                Just i -> i

        --Need to create a new variable name from this
        let new_var_name = varname ++ "_" ++ (show var_numbering)
        

        let fun_id = (mkRdrUnqual $ mkVarOcc new_var_name) :: (IdP GhcPs)
        let m_ctxt = FunRhs (noLoc fun_id) Prefix NoSrcStrict
        let m_pats = []
        let grhs = GRHS NoExtField [] (noLoc varvalue) :: GRHS GhcPs (LHsExpr GhcPs)
        let m_grhss = GRHSs NoExtField [noLoc grhs] (noLoc (EmptyLocalBinds NoExtField))
        let match_group = Match NoExtField m_ctxt [] m_grhss
        
        let fun_matches = (MG NoExtField (noLoc [noLoc match_group]) Generated) :: MatchGroup GhcPs (LHsExpr GhcPs)
        let fun_co_fn = WpHole
        let fun_tick = []
        let function = (FunBind NoExtField (noLoc fun_id) fun_matches fun_co_fn fun_tick) :: (HsBindLR GhcPs GhcPs)

        let contents = listToBag [noLoc function]
        let valbinds = (ValBinds NoExtField contents []) :: (HsValBindsLR GhcPs GhcPs)
        let hsvalbinds = HsValBinds NoExtField valbinds

        --Increment the number of the variable we've created the let statement for.
        put (Map.insert varname (var_numbering +1) var_numberings)

        --Substitute the new_var_name into the expression
        let new_expr = subValues expr (Map.fromList [(varname, (HsVar NoExtField (noLoc fun_id)))])

        return (HsLet NoExtField (noLoc hsvalbinds) (noLoc new_expr)) 


--Evaluates ambiguous arguments
evalAmbiguousArguments :: [(HsExpr GhcPs, LPat GhcPs, [LPat GhcPs])] -> ScTypes.ModuleInfo -> ScTypes.ModuleInfo -> DynFlags -> StateT EvalState IO([(HsExpr GhcPs)], TraverseResult)
evalAmbiguousArguments ((expr, pattern, patterns): args) modu hidden flags = do 
    
    --Check to see which of the patterns 
    let patstring = showSDocUnsafe $ ppr pattern
    if (and $ map (\pat -> (showSDocUnsafe $ ppr pat) == patstring) patterns) 
        then do --Go and check the other results.
            (newargs, result) <- evalAmbiguousArguments args modu hidden flags
            return (expr:newargs, result)
        else do 
            ((L _ newarg), result) <- evalExpr (noLoc expr) modu hidden flags
            case result of 
                Reduced -> return (newarg:(map (\(x,_,_)->x) args), Reduced)
                _ -> do 
                    (newargs, result) <- evalAmbiguousArguments args modu hidden flags
                    return (expr:newargs, result)
evalAmbiguousArguments [] _ _ _ = return ([], NotFound)

--Evaluate the first argument which doesn't pattern match with the proper pattern
evalNonMatchingArguments :: [(HsExpr GhcPs, LPat GhcPs)] -> ScTypes.ModuleInfo -> ScTypes.ModuleInfo -> DynFlags -> StateT EvalState IO([(HsExpr GhcPs)], TraverseResult)
evalNonMatchingArguments ((expr, pattern): args) modu hidden flags = do 
    possiblematch <- lift $ FormalActualMap.matchPattern expr pattern modu
    case possiblematch of 
        Nothing -> do 
            ((L _ newarg), result) <- evalExpr (noLoc expr) modu hidden flags
            return (newarg:(map fst args), result)
        _ -> do 
            (newargs, result) <- evalNonMatchingArguments args modu hidden flags
            return (expr:newargs, result)
evalNonMatchingArguments [] _ _ _ = return ([], NotFound)