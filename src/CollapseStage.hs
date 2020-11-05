{-# LANGUAGE PackageImports, TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module CollapseStage where 

import "ghc-lib-parser" GHC.Hs
import "ghc-lib-parser" SrcLoc
import "ghc-lib-parser" RdrName
import "ghc-lib-parser" OccName
import "ghc-lib-parser" Outputable

import qualified Data.Map.Strict as Map
import Data.List
import Data.Either

import Tools
import ScTypes

data CollapseResult = NotCollapsed | Collapsed  
    deriving Eq

--Takes the fully expanded statement and collapses it into one step by step
--Doesn't print the first time around
collapse :: (LHsDecl GhcPs) -> IO(Bool)
collapse decl = do 
    (decl', result) <- collapseDecl decl
    case result of 
        Collapsed -> do 
            collapseprint decl'
            return True
        _ -> 
            return False

collapseprint :: (LHsDecl GhcPs) -> IO()
collapseprint decl = do 
    (decl', result) <- collapseDecl decl
    case result of 
        Collapsed -> do 
            putStrLn $ "   =  " ++ (showSDocUnsafe $ ppr decl)
            collapseprint decl' 
        _ -> return ()

collapseDecl :: (LHsDecl GhcPs) -> IO((LHsDecl GhcPs),CollapseResult)
collapseDecl (L l(SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr)) g ))) = do 
    (expr',  result) <- collapseStep expr 
    let decl' =  (L l (SpliceD a (SpliceDecl b (L c (HsUntypedSplice d e f expr')) g )))
    return (decl', result)

collapseStep :: (LHsExpr GhcPs) -> IO((LHsExpr GhcPs),CollapseResult)
collapseStep (L l (HsPar xpar expr)) = do 
    (expr', result) <- collapseStep expr
    return ((L l (HsPar xpar expr')),result)

collapseStep (L l (ExplicitList xlist m elems)) = do 
    res <- mapM collapseStep elems
    let (elems', results) = unzip res

    if (elem Collapsed results) 
        then 
            return (L l (ExplicitList xlist m elems'), Collapsed)
        else  
            return (L l (ExplicitList xlist m elems), NotCollapsed)

collapseStep (L l (HsApp xApp lhs rhs)) = do 
    (rhs', resultrhs) <- collapseStep rhs 
    case resultrhs of 
        Collapsed -> return ((L l (HsApp xApp lhs rhs')), Collapsed) --If the rhs has collapsed return it
        NotCollapsed -> do 
            (lhs', resultlhs) <- collapseStep lhs 
            case resultlhs of 
                Collapsed -> return ((L l (HsApp xApp lhs' rhs)), Collapsed) --If the lhs has collapsed return it
                NotCollapsed -> do 
                    --Try and execute the application
                    let funstring = showSDocUnsafe $ ppr (L l (HsApp xApp lhs rhs))
                    eResult <- Tools.evalAsString funstring
                    case eResult of 
                        (Left _) -> return ((L l (HsApp xApp lhs rhs)), NotCollapsed)
                        (Right out) -> return ((L l (Tools.stringtoId out)), Collapsed)

collapseStep (L l (OpApp xop lhs op rhs)) = do 
    (rhs', resultrhs) <- collapseStep rhs 
    case resultrhs of 
        Collapsed -> return ((L l (OpApp xop lhs op rhs')), Collapsed) --If the rhs has collapsed return it
        NotCollapsed -> do 
            (lhs', resultlhs) <- collapseStep lhs 
            case resultlhs of 
                Collapsed -> return ((L l (OpApp xop lhs' op rhs)), Collapsed) --If the lhs has collapsed return it
                NotCollapsed -> do 
                    --Try and execute the application
                    let funstring = showSDocUnsafe $ ppr (L l (OpApp xop lhs op rhs))
                    eResult <- Tools.evalAsString funstring
                    case eResult of 
                        (Left _) -> return ((L l (OpApp xop lhs' op rhs')), NotCollapsed)
                        (Right out) -> return ((L l (Tools.stringtoId out)), Collapsed)




collapseStep expr = return (expr, NotCollapsed)