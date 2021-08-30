{-# LANGUAGE PackageImports, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module EvalStage where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable
import "ghc-lib-parser" DynFlags


import qualified Data.Map.Strict as Map
import Data.List
import Data.Either
import Data.Char
import Data.Maybe

import Tools 
import ScTypes
import FormalActualMap
import DefinitionGetter
import NormalFormReducer 


--The Int is how many variables are bound to the Found function
--The String is the name of the function 
data TraverseResult = Reduced | NotFound | Found Int String | Constructor

--Execute the computation fully
execute :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> String -> DynFlags -> IO(LHsDecl GhcPs)
execute decl funMap prevline flags = do 
  (newdecl, changed) <- EvalStage.evalDecl decl funMap flags
  case changed of 
      Reduced -> do 
        let newline = (showSDocUnsafe $ ppr newdecl)
        
        if (newline /= prevline) then do
            let newlines = lines newline 
            putStrLn $ "   =  " ++ (head newlines)

            mapM_ (\x -> putStrLn ("      " ++ x)) (tail newlines) --Print the other lines


            else do 
                return ()
        execute newdecl funMap newline flags 
      _ -> do
        return $ decl

--Do one stage of evaluation on the Decl -- Has to be IO as we make calls to GHCi
evalDecl :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> DynFlags -> IO(LHsDecl GhcPs, TraverseResult)
evalDecl (L l(SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr)) g ))) func flags = do 
    (expr', result) <- evalExpr expr func flags
    let decl' = (L l (SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr')) g ))) --Return our declaration to the correct context
    return (decl', result)
evalDecl _ _ _ = error "Should be evaluating SpliceD"

--Evaluating an expression
-- Will be evaluating the LHS of any expression first, so only one will be expanded at a time
--Each case will be a bit different
evalExpr :: (LHsExpr GhcPs) -> ScTypes.ModuleInfo -> DynFlags -> IO(LHsExpr GhcPs, TraverseResult)

--Found a variable, if it is one of our functions, return we have found it
--If it is one of our varibles then do a substitution for the value
evalExpr var@(L l (HsVar xVar id)) funcMap flags  = do
    let name = showSDocUnsafe $ ppr id 

    if (isUpper $ head $ name)
        then return (var, Constructor)
    else
        if (Map.member name funcMap)
            then do 
                let (FunctionInfo _ _ _ n) = funcMap Map.! name 
                if (n == 0) 
                    then do 
                        expr <- evalApp (L l (HsVar xVar id)) funcMap flags
                        return (expr, Reduced) --This is a variable with 0 arguments
                    else return ((L l (HsVar xVar id)), Found 0 name) --This is a function which requires more arguments
            else do 
                return (var, NotFound)     

--Applicaton statement 
evalExpr application@(L l (HsApp xApp lhs rhs)) funcMap flags = do 
    (lhs' , lhsresult) <- evalExpr lhs funcMap flags --Traverse the lhs
    (rhs' , rhsresult) <- evalExpr rhs funcMap flags-- Traverse the rhs
    case lhsresult of 
        (Found i name) -> do 
            argsNeeded <- case (funcMap Map.!? name) of 
                (Just (FunctionInfo _ _ _ n))  -> return n 
                _ -> error $ Tools.errorMessage ++ name ++ " not found in funcMap - evalExpr" 

            if (argsNeeded == (i + 1)) -- +1 because including the argument in the rhs of this application
                then do
                    newexpr <- evalApp application funcMap flags
                    return (newexpr,  Reduced) -- Evaluate this application
            else return (application, (Found (i+1) name)) --Go up a level and try and find more argument

        NotFound -> do --In this case explore the rhs
            case rhsresult of 
                Reduced -> do 
                    let newApp = (L l (HsApp xApp lhs (removeLPars rhs')))
                    return (newApp, rhsresult)
                -- Attempt to evaluate
                _ -> do 
                    collapsed <- NormalFormReducer.reduceNormalForm application flags 

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

evalExpr application@(L l (OpApp xop lhs op rhs)) funcMap flags = do 
    (op', opresult) <- evalExpr op funcMap flags -- Try and reduce the op.

    case opresult of 
        Reduced -> return ((L l (OpApp xop lhs op' rhs)), Reduced)
        _ -> do 
            (lhs' , lhsresult) <- evalExpr lhs funcMap flags--Traverse the lhs
        
            let thisApp = (L l (OpApp xop lhs' op rhs))
            
            (hsapp, found) <- case lhsresult of 
                Reduced -> return (thisApp, Reduced) 
                _ -> do 
                    (rhs', rhsresult) <- evalExpr rhs funcMap flags --Traverse rhs 
                    case rhsresult of 
                        Reduced -> do
                            return (L l (OpApp xop lhs' op rhs'), rhsresult)
                        _ -> do
                            let funname = showSDocUnsafe $ ppr $ op

                            if (Map.member funname funcMap)
                                then do
                                    newexpr <- evalApp (L l (HsApp NoExtField (L l (HsApp NoExtField op lhs)) rhs)) funcMap flags --Treat it as a prefix operation
                                    
                                    return (newexpr, Reduced)
                                else do
                                    reduced <- NormalFormReducer.reduceNormalForm application flags 
                                    case reduced of 
                                        Nothing -> return (application, NotFound)
                                        (Just normal) -> return (normal, Reduced)
                    
            return (hsapp, found)

--Deal with parentheses 
evalExpr (L l (HsPar xpar expr)) funcMap flags = do 
    (expr', found) <- evalExpr expr funcMap flags 
    return ((L l (Tools.removePars (HsPar xpar expr'))), found)

--Deal with if/else statement
evalExpr orig@(L l (HsIf xif syn cond lhs rhs)) funcMap flags = do 

    let condstr = showSDocUnsafe $ ppr $ Tools.removeLPars cond 

    case condstr of 
        "True" -> return (lhs, Reduced) 
        "False" -> return (rhs, Reduced) 
        _ -> do 
            (cond' , replaced) <- evalExpr cond funcMap flags

            case replaced of 
                Reduced -> return ((L l (HsIf xif syn cond' lhs rhs)), Reduced)
                _ -> do 
                    collapsed <- NormalFormReducer.reduceNormalForm cond flags 
                    case collapsed of 
                        (Just cond'') -> return ((L l (HsIf xif syn cond'' lhs rhs)), Reduced) 
                        _ -> return (orig, NotFound)
                        
--Deal with lists
evalExpr (L l (ExplicitList xep msyn (expr:exprs))) funcMap flags= do 
    (expr' , replaced) <- evalExpr expr funcMap flags 

    case replaced of 
        Reduced -> return  ((L l (ExplicitList xep msyn (expr':exprs))), Reduced)

        _ -> do 
            ((L l (ExplicitList _ _ exprs')), replaced') <- evalExpr (L l (ExplicitList xep msyn exprs)) funcMap flags 
            return ((L l (ExplicitList xep msyn (expr:exprs'))), replaced')

evalExpr (L l (ExplicitList xep msyn [])) _ _ = do 
    return ((L l (ExplicitList xep msyn [])), NotFound)

--Deal with tuples
evalExpr (L l (ExplicitTuple xtup (expr:exprs) box)) funcMap flags = do 
    case expr of 
        (L l' (Present xpres tupexp)) -> do  
            (expr' , replaced) <- evalExpr tupexp funcMap flags 
            case replaced   of 
                Reduced -> do 
                    let tuple = (L l' (Present xpres expr'))
                    return  ((L l (ExplicitTuple xtup (tuple:exprs) box)), Reduced)

                _ -> do 
                    ((L l (ExplicitTuple _ exprs' _)), replaced') <- evalExpr (L l (ExplicitTuple xtup exprs box)) funcMap flags 
                    return ((L l (ExplicitTuple xtup (expr:exprs') box)), replaced')
        
        _ -> do 
            ((L l (ExplicitTuple _ exprs' _)), replaced') <- evalExpr (L l (ExplicitTuple xtup exprs box)) funcMap flags 
            return ((L l (ExplicitTuple xtup (expr:exprs') box)), replaced')

evalExpr (L l (ExplicitTuple xtup [] box)) _ _ = do 
    return ((L l (ExplicitTuple xtup [] box)), NotFound)

--List comprehensions
evalExpr comp@(L l (HsDo xDo ListComp (L l' (stmt: stmts)))) funcMap flags = do 
    case stmt of 
        
        -- Try and pattern match (x:xs) against it. If this fails then attempt to expand it. 
        -- Need to work out if it is empty? 
        -- Utilise the definition getter for this work. 
        
        (L l (BindStmt a pat lexpr@(L _ expr) e f)) -> do 
            
            exprNotEmpty <- matchesPattern expr "(x:xs)" funcMap
            
            if (not exprNotEmpty) then 
                -- Returns an empty list.
                return ((L l (ExplicitList NoExtField Nothing [])), Reduced)
            else do 
                maybehead <- FormalActualMap.splitList lexpr funcMap
                case maybehead of 
                    Nothing -> do 
                        (newexpr, res) <- evalExpr lexpr funcMap flags 
                        let newstmt = (L l (BindStmt a pat newexpr e f))
                        let newcomp = ((L l (HsDo xDo ListComp (L l' (newstmt: stmts)))))
                        return (newcomp, res)
                    
                    Just (headexpr, tailexpr) -> do 
                        let newcomp = (HsDo xDo ListComp (L l' stmts))
                        map <- FormalActualMap.matchPatternL headexpr pat funcMap

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
            (condition', replaced) <- evalExpr condition funcMap flags --Evaluate the condition

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

evalExpr lit@(L l (HsLit xlit hslit)) _ _= return (lit, NotFound)

evalExpr lit@(L l (HsOverLit xlit hslit)) _ _= return (lit, NotFound)

evalExpr (L l (NegApp xneg expr syn)) funcMap flags = do 
    (newexp, result) <- evalExpr expr funcMap flags   

    return ((L l (NegApp xneg newexp syn)), result)

evalExpr arith@(L _ (ArithSeq _ _ _)) _ _ = return (arith, NotFound) --Currently not trying to reduce any of the terms in the sequence 

evalExpr expr _ flags = do --If not defined for then make an attempt to reduce to normal form    
    result <- NormalFormReducer.reduceNormalForm expr flags
    
    case result of 
        Nothing -> return (expr, NotFound)
        (Just normal) -> return (normal, Reduced)

--Evaluates a function (one step)
--Presumes it is a function applied to the correct number of args
--Currently assumes the function is not within some parenthesis (bad assumption)
evalApp :: (LHsExpr GhcPs) -> (ScTypes.ModuleInfo) -> DynFlags -> IO(LHsExpr GhcPs)
evalApp (L l expr@(HsApp xapp lhs rhs)) modu flags = do 
        let (func, args) = Tools.getFuncArgs (L l expr) --(head exprs, tail exprs) --Get the expression(s) for the function and the arguments 
        (def, pattern) <- DefinitionGetter.getDef func args modu --Get the appropriate rhs given the arguments 
        valmap <- FormalActualMap.matchPatterns args pattern modu -- Get the appropriate formal-actual mapping given the arguments 
        
        if (isNothing valmap) then do 
            (lhs', lhsresult) <- evalExpr lhs modu flags
            case lhsresult of 
                Reduced -> do 
                    return (L l (HsApp xapp lhs' rhs))
                _ -> do 
                    (rhs', rhsresult) <- evalExpr rhs modu flags
                    case rhsresult of 
                        Reduced -> do 
                            return (L l (HsApp xapp lhs rhs'))
                        _ -> do 
                            error "Fault with pattern matching"
        else do 
            let expr' = subValues def (fromJust valmap) --Substitute formals for actuals 
            return (L l expr')
evalApp (L l expr@(HsVar _ _ )) modu _ = do 
    (def, _) <- DefinitionGetter.getDef expr [] modu
    return (L l def)


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