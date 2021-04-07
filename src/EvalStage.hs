{-# LANGUAGE PackageImports, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module EvalStage where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

import qualified Data.Map.Strict as Map
import Data.List
import Data.Either
import Data.Char

import Tools 
import ScTypes
import FormalActualMap
import DefinitionGetter
import CollapseStage

--The Int is how many variables are bound to the Found function
--The String is the name of the function 
data TraverseResult = Reduced | NotFound | Found Int String | Constructor

--Execute the computation fully
execute :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> String -> IO(LHsDecl GhcPs)
execute decl funMap prevline = do 
  (newdecl, changed) <- EvalStage.evalDecl decl funMap 
  case changed of 
      Reduced -> do 
        let newline = (showSDocUnsafe $ ppr newdecl)
        
        if (newline /= prevline) then do
            let newlines = lines newline 
            putStrLn $ "   =  " ++ (head newlines)

            mapM_ (\x -> putStrLn ("      " ++ x)) (tail newlines) --Print the other lines


            else do 
                return ()
        execute newdecl funMap newline
      _ -> do
        return $ decl

--Do one stage of evaluation on the Decl -- Has to be IO as we make calls to GHCi
evalDecl :: (LHsDecl GhcPs) -> ScTypes.ModuleInfo -> IO(LHsDecl GhcPs, TraverseResult)
evalDecl (L l(SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr)) g ))) func = do 
    (expr', result) <- evalExpr expr func 
    let decl' = (L l (SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr')) g ))) --Return our declaration to the correct context
    return (decl', result)
evalDecl _ _ = error "Should be evaluating SpliceD"

--Evaluating an expression
-- Will be evaluating the LHS of any expression first, so only one will be expanded at a time
--Each case will be a bit different
evalExpr :: (LHsExpr GhcPs) -> ScTypes.ModuleInfo -> IO(LHsExpr GhcPs, TraverseResult)

--Found a variable, if it is one of our functions, return we have found it
--If it is one of our varibles then do a substitution for the value
evalExpr var@(L l (HsVar xVar id)) funcMap = do
    let name = showSDocUnsafe $ ppr id 

    if (isUpper $ head $ name)
        then return (var, Constructor)
    else
        if (Map.member name funcMap)
            then do 
                let (FunctionInfo _ _ _ n) = funcMap Map.! name 
                if (n == 0) 
                    then do 
                        expr <- evalApp (L l (HsVar xVar id)) funcMap
                        return (expr, Reduced) --This is a variable with 0 arguments
                    else return ((L l (HsVar xVar id)), Found 0 name) --This is a function which requires more arguments
            else do 
                return (var, NotFound)     

--Applicaton statement 
evalExpr application@(L l (HsApp xApp lhs rhs)) funcMap = do 
    (lhs' , lhsresult) <- evalExpr lhs funcMap --Traverse the lhs
    (rhs' , rhsresult) <- evalExpr rhs funcMap -- Traverse the rhs
    case lhsresult of 
        (Found i name) -> do 
            case rhsresult of 
                Reduced -> return ((L l (HsApp xApp lhs rhs')), Reduced)
                
                Constructor -> do
                    argsNeeded <- case (funcMap Map.!? name) of 
                        (Just (FunctionInfo _ _ _ n))  -> return n 
                        _ -> error $ Tools.errorMessage ++ name ++ " not found in funcMap - evalExpr" 

                    if (argsNeeded == (i + 1)) -- +1 because including the argument in the rhs of this application
                        then do
                            newexpr <- evalApp application funcMap
                            return (newexpr,  Reduced) -- Evaluate this application
                    else return (application, (Found (i+1) name)) --Go up a level and try and find more argument

                _ -> do 
                    
                    (rhs'', rhsresult') <- CollapseStage.collapseStep rhs --See if the rhs argument needs to be collapsed 

                    case rhsresult' of 
                        Collapsed -> return ((L l (HsApp xApp lhs rhs'')), Reduced) --The argument can be collapsed
                        NotCollapsed -> do 
                            argsNeeded <- case (funcMap Map.!? name) of 
                                (Just (FunctionInfo _ _ _ n))  -> return n 
                                _ -> error $ Tools.errorMessage ++ name ++ " not found in funcMap - evalExpr" 

                            if (argsNeeded == (i + 1)) -- +1 because including the argument in the rhs of this application
                                then do
                                    newexpr <- evalApp application funcMap
                                    return (newexpr,  Reduced) -- Evaluate this application
                            else return (application, (Found (i+1) name)) --Go up a level and try and find more argument

        NotFound -> do --In this case explore the rhs
            case rhsresult of 
                Reduced -> do 
                    let newApp = (L l (HsApp xApp lhs (removeLPars rhs')))
                    return (newApp, rhsresult)
                -- Attempt to evaluate
                _ -> do 
                    (expr, result) <- CollapseStage.collapseStep application
                    case result of 
                        Collapsed -> do 
                            return (expr, Reduced)
                        _ -> do
                            return (application, NotFound)
        
        Constructor -> do --In this case a constructor.
            case rhsresult of
                Reduced -> do 
                    let newApp = (L l (HsApp xApp lhs (removeLPars rhs')))
                    return (newApp, Reduced)
                _ -> 
                    return (application, Constructor)

        _ -> return ((L l (HsApp xApp lhs' rhs)), lhsresult)

evalExpr application@(L l (OpApp xop lhs op rhs)) funcMap = do 
    (op', opresult) <- evalExpr op funcMap -- Try and reduce the op.

    case opresult of 
        Reduced -> return ((L l (OpApp xop lhs op' rhs)), Reduced)
        _ -> do 
            (lhs' , lhsresult) <- evalExpr lhs funcMap --Traverse the lhs
        
            let thisApp = (L l (OpApp xop lhs' op rhs))
            
            (hsapp, found) <- case lhsresult of 
                Reduced -> return (thisApp, Reduced) 
                _ -> do 
                    (rhs', rhsresult) <- evalExpr rhs funcMap --Traverse rhs 
                    case rhsresult of 
                        Reduced -> do
                            return (L l (OpApp xop lhs' op rhs'), rhsresult)
                        _ -> do
                            let funname = showSDocUnsafe $ ppr $ op

                            if (Map.member funname funcMap)
                                then do
                                    newexpr <- evalApp (L l (HsApp NoExtField (L l (HsApp NoExtField op lhs)) rhs)) funcMap --Treat it as a prefix operation
                                    
                                    return (newexpr, Reduced)
                                else do
                                    eResult <- Tools.evalAsString $ showSDocUnsafe $ ppr application 
                                    case eResult of 
                                        (Left _) -> return (application, NotFound)
                                        (Right out) -> return ((L l (Tools.stringtoId out)), Reduced) 
                    
            return (hsapp, found)

--Deal with parentheses 
evalExpr (L l (HsPar xpar expr)) funcMap = do 
    (expr', found) <- evalExpr expr funcMap
    return ((L l (Tools.removePars (HsPar xpar expr'))), found)

--Deal with if/else statement
evalExpr (L l (HsIf xif syn cond lhs rhs)) funcMap = do 
    (cond' , replaced) <- evalExpr cond funcMap 

    case replaced of 
        Reduced -> return ((L l (HsIf xif syn cond' lhs rhs)), Reduced)

        _ -> do 
            (cond'' , collapsed) <- CollapseStage.collapseStep cond

            case collapsed of 
                Collapsed -> return ((L l (HsIf xif syn cond'' lhs rhs)), Reduced) 
                
                _ -> do 
                    let condstring = showSDocUnsafe $ ppr cond
                    condresult <- Tools.evalAsString condstring

                    case condresult of 
                        (Right str) -> return $ if (str == "True") then (lhs, Reduced) else (rhs, Reduced)

                        _ -> return ((L l (HsIf xif syn cond lhs rhs)), NotFound) --In theory we should not get this  
        
--Deal with lists
evalExpr (L l (ExplicitList xep msyn (expr:exprs))) funcMap = do 
    (expr' , replaced) <- evalExpr expr funcMap

    case replaced of 
        Reduced -> return  ((L l (ExplicitList xep msyn (expr':exprs))), Reduced)

        _ -> do 
            ((L l (ExplicitList _ _ exprs')), replaced') <- evalExpr (L l (ExplicitList xep msyn exprs)) funcMap
            return ((L l (ExplicitList xep msyn (expr:exprs'))), replaced')

evalExpr (L l (ExplicitList xep msyn [])) _ = do 
    return ((L l (ExplicitList xep msyn [])), NotFound)

--Deal with tuples
evalExpr (L l (ExplicitTuple xtup (expr:exprs) box)) funcMap = do 
    case expr of 
        (L l' (Present xpres tupexp)) -> do  
            (expr' , replaced) <- evalExpr tupexp funcMap

            case replaced   of 
                Reduced -> do 
                    let tuple = (L l' (Present xpres expr'))
                    return  ((L l (ExplicitTuple xtup (tuple:exprs) box)), Reduced)

                _ -> do 
                    ((L l (ExplicitTuple _ exprs' _)), replaced') <- evalExpr (L l (ExplicitTuple xtup exprs box)) funcMap
                    return ((L l (ExplicitTuple xtup (expr:exprs') box)), replaced')
        
        _ -> do 
            ((L l (ExplicitTuple _ exprs' _)), replaced') <- evalExpr (L l (ExplicitTuple xtup exprs box)) funcMap
            return ((L l (ExplicitTuple xtup (expr:exprs') box)), replaced')

evalExpr (L l (ExplicitTuple xtup [] box)) _ = do 
    return ((L l (ExplicitTuple xtup [] box)), NotFound)

--List comprehensions
evalExpr comp@(L l (HsDo xDo ListComp (L l' (stmt: stmts)))) funcMap = do 

    case stmt of 
        (L l (BindStmt a pat (L b (ExplicitList c d (x:xs))) e f)) ->  do --Generators 
            let newcomp = (HsDo xDo ListComp (L l' stmts))
            let var = showSDocUnsafe $ ppr $ pat
            let newvmap = (\(L _ expr) -> Map.fromList [(var, expr)]) x
            
            --Create the new lists 
            let newlistcomps = (\v -> (L l (subValues newcomp v))) newvmap
            --If any of them are finished convert them to plain lists
            let finallistcomp = listCompFinished newlistcomps

            if not (null xs) then do 
                let newstmts = (L l (BindStmt a pat (L b (ExplicitList c d xs)) e f)) : stmts

                --Combine them together
                let finalexpr = combineLists [finallistcomp, (L l (HsDo xDo ListComp (L l' newstmts)))]

                return (finalexpr, Reduced)
            else do 
                return (finallistcomp, Reduced) 
        
        (L l (BindStmt a pat expr e f)) -> do --In this case we have some kind of expression here (in the generator)
            (expr' , replaced) <- evalExpr expr funcMap
            let newstmts = (L l (BindStmt a pat expr' e f)) : stmts
            let newcomp = (L l (HsDo xDo ListComp (L l' newstmts)))
            
            case replaced of 
                Reduced -> return (newcomp, replaced)
                _ -> do 
                    eResult <- Tools.evalAsString $ showSDocUnsafe $ ppr comp 
                    case eResult of 
                        (Left _) -> return (comp, NotFound)
                        (Right out) -> return ((L l (Tools.stringtoId out)), Reduced) 
        
        (L l (BodyStmt ext condition lexpr rexpr)) -> do
            (condition', replaced) <- evalExpr condition funcMap --Evaluate the condition

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

evalExpr lit@(L l (HsLit xlit hslit)) _ = return (lit, NotFound)

evalExpr lit@(L l (HsOverLit xlit hslit)) _ = return (lit, NotFound)

evalExpr (L l (NegApp xneg expr syn)) funcMap = do 
    (newexp, result) <- evalExpr expr funcMap   

    return ((L l (NegApp xneg newexp syn)), result)

evalExpr lexpr@(L l expr) _ = do --If not defined for then make an attempt to reduce to normal form
    result <- Tools.evalAsString $ showSDocUnsafe $ ppr expr
    
    case result of 
        (Left _) -> return (lexpr, NotFound)
        (Right out) -> return ((L l (Tools.stringtoId out)), Reduced) 

--Evaluates a function (one step)
--Presumes it is a function applied to the correct number of args
--Currently assumes the function is not within some parenthesis (bad assumption)
evalApp :: (LHsExpr GhcPs) -> (ScTypes.ModuleInfo) -> IO(LHsExpr GhcPs)
evalApp (L l expr) modu = do 
        --let exprs = Tools.getValuesInApp (L l expr) --Get the sub expressions in the expression 
        let (func, args) = Tools.getFuncArgs (L l expr) --(head exprs, tail exprs) --Get the expression(s) for the function and the arguments 
        def <- DefinitionGetter.getDef func args modu --Get the appropriate rhs given the arguments 
        valmap <- FormalActualMap.getMap func args modu -- Get the appropriate formal-actual mapping given the arguments 
        let expr' = subValues def valmap --Substitute formals for actuals 
        return (L l expr')


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