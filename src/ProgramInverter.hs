{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ProgramInverter ( invert ) where

import AST
import ClassAnalyzer
import ScopeAnalyzer
import Control.Monad.Except
import Data.List

import Debug.Trace (trace, traceShow)
import Control.Monad.Reader
import Stringify

newtype ProgramInverter a = ProgramInverter { runIV :: ReaderT Int (Except String) a }
    deriving (Functor, Applicative, Monad, MonadReader Int, MonadError String)

tab :: Int -> String
tab n
    | n == 0 = ""
    | n == 1 = "    "
    | otherwise = "    " ++ tab (n - 1)

newlines :: Int -> [String] -> String
newlines n a = intercalate "\n" $ map (tab n ++) a

newlines2 :: Int -> [String] -> String
newlines2 n a = intercalate "\n\n" $ map (tab n ++) a

ivExpression :: Expression -> ProgramInverter String
ivExpression (Constant n) = return $ show n
ivExpression (Variable v) = return v
ivExpression (ArrayElement (n, e)) = 
    ivExpression e >>= \e' ->
        return $ n ++ "[" ++ e' ++ "]"
ivExpression Nil = return "nil"
ivExpression (Binary binop e1 e2) = do
    e1' <- ivExpression e1
    e2' <- ivExpression e2
    let binop' = stringifyBinOp binop
     in return $ unwords [e1', binop', e2']

ivVariable :: (Identifier, Maybe Expression) -> ProgramInverter String
ivVariable (n, Nothing) = return n
ivVariable (n, Just e)  = ivExpression $ ArrayElement (n, e)

ivStatement :: Statement -> ProgramInverter String
ivStatement (Assign n modop e) = do
    e' <- ivExpression e
    let modop' = stringifyModOp modop
     in return $ unwords [n, modop', e']
ivStatement (AssignArrElem e1 modop e2) = do
    e1' <- ivExpression $ ArrayElement e1
    e2' <- ivExpression e2
    let modop' = stringifyModOp modop
     in return $ unwords [e1', modop', e2']
ivStatement (Swap v1 v2) = do
    v1' <- ivVariable v1 
    v2' <- ivVariable v2
    return $ unwords [v1', "<=>", v2']
ivStatement (Conditional e1 s1 s2 e2) = do
    cl <- ask
    e1' <- ivExpression e1
    s1' <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse s1)
    s2' <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse s2)
    e2' <- ivExpression e2
    let enc = unwords ["if", e2', "then"]
        els = tab (cl - 1) ++ "else"
        exc = tab (cl - 1) ++ unwords ["fi", e1']
     in return $ intercalate "\n" [enc, s1', els, s2', exc]
ivStatement (Loop e1 s1 s2 e2) = do
    cl <- ask
    e1' <- ivExpression e1
    s1' <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse s1)
    s2' <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse s2)
    e2' <- ivExpression e2
    let enc = unwords ["from", e2', "do"]
        lp  = tab (cl - 1) ++ "loop"
        exc = tab (cl - 1) ++ unwords ["until", e1']
     in return $ intercalate "\n" [enc, s1', lp, s2', exc]
ivStatement (ObjectBlock ot n s) = do
    cl <- ask
    s' <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse s)
    let enc = unwords ["construct", ot, n]
        exc = tab (cl - 1) ++ unwords ["destruct", n]
     in return $ intercalate "\n" [enc, s', exc]
ivStatement (LocalBlock dt n e1 s e2) = do
    cl <- ask
    e1' <- ivExpression e1
    s'  <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse s)
    e2' <- ivExpression e2
    let dt' = stringifyDataType dt
        enc = unwords ["local", dt', n, "=", e2']
        exc = tab (cl - 1) ++ unwords ["delocal", dt', n, "=", e1']
     in return $ intercalate "\n" [enc, s', exc]
ivStatement (LocalCall m args) = do
    args' <- intercalate ", " <$> mapM ivVariable args 
    let args'' = "(" ++ args' ++ ")"
     in return $ unwords ["uncall", m ++ args'']
ivStatement (LocalUncall m args) = do
    args' <- intercalate ", " <$> mapM ivVariable args 
    let args'' = "(" ++ args' ++ ")"
     in return $ unwords ["call", m ++ args'']
ivStatement (ObjectCall o m args) = do
    o' <- ivVariable o
    args' <- intercalate ", " <$> mapM ivVariable args
    let args'' = "(" ++ args' ++ ")"
     in return $ unwords ["uncall", o' ++ "::" ++ m ++ args'']
ivStatement (ObjectUncall o m args) = do
    o' <- ivVariable o
    args' <- intercalate ", " <$> mapM ivVariable args 
    let args'' = "(" ++ args' ++ ")"
     in return $ unwords ["call", o' ++ "::" ++ m ++ args'']
ivStatement (ObjectConstruction tn o) = do
    o' <- ivVariable o
    return $ unwords ["delete", tn, o']
ivStatement (ObjectDestruction tn o) = do
    o' <- ivVariable o
    return $ unwords ["new", tn, o']
ivStatement (CopyReference dt v1 v2) = do
    v1' <- ivVariable v1
    v2' <- ivVariable v2
    let dt' = stringifyDataType dt
     in return $ unwords ["uncopy", dt', v1', v2']
ivStatement (UnCopyReference dt v1 v2) = do
    v1' <- ivVariable v1
    v2' <- ivVariable v2
    let dt' = stringifyDataType dt
     in return $ unwords ["copy", dt', v1', v2']
ivStatement (ArrayConstruction (tn, e) n) = do
    ivExpression (ArrayElement (tn, e)) >>= \arr ->
        return $ unwords ["delete", arr, n]
ivStatement (ArrayDestruction (tn, e) n) = do
    arr <- ivExpression $ ArrayElement (tn, e)
    return $ unwords ["new", arr, n]
ivStatement Skip = return "skip"

ivField :: VariableDeclaration -> ProgramInverter String
ivField (GDecl dt fn) = do
    let dt' = stringifyDataType dt
     in return $ unwords [dt', fn]

ivMethod :: MethodDeclaration -> ProgramInverter String
ivMethod (GMDecl mn [] b) = do
    cl <- ask
    b' <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse b)
    let mn' = "method " ++ mn ++ "()"
     in return $ intercalate "\n" [mn', b']
ivMethod (GMDecl mn ps b) = do
    cl <- ask
    ps' <- intercalate ", " <$> mapM ivField ps
    b'  <- newlines cl <$> incLevel cl (mapM ivStatement $ reverse b)
    let ps'' = "(" ++ ps' ++ ")"
        mn' = "method " ++ mn ++ ps''
     in return $ intercalate "\n" [mn', b']

ivClassDeclaration :: ClassDeclaration -> ProgramInverter String
ivClassDeclaration (GCDecl cn Nothing [] ms) = do
    cl <- ask
    ms' <- newlines2 cl <$> incLevel cl (mapM ivMethod ms)
    let cn' = "class " ++ cn
     in return $ intercalate "\n" [cn', "", ms']
ivClassDeclaration (GCDecl cn Nothing fs ms) = do
    cl <- ask
    fs' <- newlines cl <$> incLevel cl (mapM ivField fs)
    ms' <- newlines2 cl <$> incLevel cl (mapM ivMethod ms)
    let cn' = "class " ++ cn
     in return $ intercalate "\n" [cn', fs', "", ms']
ivClassDeclaration (GCDecl cn (Just i) fs ms) = do
    cl <- ask
    fs' <- newlines cl <$> incLevel cl (mapM ivField fs)
    ms' <- newlines2 cl <$> incLevel cl (mapM ivMethod ms)
    let cn' = "class " ++ cn ++ " inherits " ++ i
     in return $ intercalate "\n" [cn', fs', "", ms']

ivClass :: (TypeName, ClassDeclaration) -> ProgramInverter String
ivClass (_, gcd) = ask >>= \cl ->
    incLevel cl $ ivClassDeclaration gcd

incLevel :: Int -> ProgramInverter a -> ProgramInverter a
incLevel c = local (const $ c + 1)

ivProgram :: SAState -> ProgramInverter String
ivProgram s = 
    let cls = reverse . classes . caState $ s
     in intercalate "\n\n" <$> mapM ivClass cls

invert :: (SProgram, SAState) -> Except String String
invert (_, s) = runReaderT (runIV $ ivProgram s) 0