{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Interpreter (interpret) where

import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bits

import AST
import ScopeAnalyzer
import Control.Monad.State

import Debug.Trace (trace, traceShow)

type Env = Map SIdentifier SExpression

data InterpreterState =
    InterpreterState {
        program :: SProgram,
        saState :: SAState,
        env :: Env
    } deriving (Show, Eq)

newtype Interpreter a = Interpreter { runInt :: StateT InterpreterState (Except String) a }
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError String)

initialState :: SProgram -> SAState -> InterpreterState
initialState p s = 
    InterpreterState {
        program = p,
        saState = s,
        env = Map.empty
    }

addBinding :: SIdentifier -> SExpression -> Interpreter ()
addBinding n e = do
    cenv <- gets env
    let nenv = Map.insert n e cenv
     in modify $ \s -> s { env = nenv }

updateBinding :: SIdentifier -> SExpression -> Interpreter ()
updateBinding n e = do
    cenv <- gets env
    let nenv = Map.adjust (const e) n cenv
     in modify $ \s -> s { env = nenv }

lookupVariableValue :: SIdentifier -> Interpreter SExpression
lookupVariableValue v = gets env >>= \env ->
    case Map.lookup v env of
        Just e -> return e
        Nothing -> throwError "Undefined variable"

evalBinOp :: BinOp -> SExpression -> SExpression -> Interpreter SExpression
evalBinOp And _ _ = throwError "And binary operator not implemented"
evalBinOp Or _ _  = throwError "Or binary operator not implemented"
evalBinOp Div e1 e2 = do
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (e1', e2') of
        (Constant v1, Constant v2) -> if v2 /= 0 then return . Constant $ v1 `div` v2
                                                 else throwError "Division by zero"
        _ -> throwError $ "Binary operation '" ++ show e1' ++ " Div " ++ show e2' ++ "' not legal"
evalBinOp binop e1 e2 = do
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (e1', e2') of
        (Constant v1, Constant v2) -> return $ evalOp binop v1 v2
        _ -> throwError $ "Binary operation '" ++ show e1' ++ " " ++ show binop ++ " " ++ show e2' ++ "' not legal"
    where evalOp Add v1 v2      = Constant $ v1 + v2
          evalOp Sub v1 v2      = Constant $ v1 - v2
          evalOp Xor v1 v2      = Constant $ v1 `xor` v2
          evalOp Mul v1 v2      = Constant $ v1 * v2
          evalOp Mod v1 v2      = Constant $ v1 `mod` v2
          evalOp BitAnd v1 v2   = Constant $ v1 .&. v2
          evalOp BitOr v1 v2    = Constant $ v1 .|. v2
          evalOp And v1 v2      = Constant $ if v1 == 0 || v2 == 0 then 0 else 1
          evalOp Or v1 v2       = Constant $ if v1 == 0 && v2 == 0 then 0 else 1
          evalOp Lt v1 v2       = Constant $ if v1 < v2  then 1 else 0
          evalOp Gt v1 v2       = Constant $ if v1 > v2  then 1 else 0
          evalOp Eq v1 v2       = Constant $ if v1 == v2 then 1 else 0
          evalOp Neq v1 v2      = Constant $ if v1 /= v2 then 1 else 0
          evalOp Lte v1 v2      = Constant $ if v1 <= v2 then 1 else 0
          evalOp Gte v1 v2      = Constant $ if v1 >= v2 then 1 else 0

evalExpression :: SExpression -> Interpreter SExpression
evalExpression (Constant n) = return $ Constant n
evalExpression (Variable v) = lookupVariableValue v
evalExpression Nil = return $ Constant 0
evalExpression (Binary binop e1 e2) = evalBinOp binop e1 e2

evalAssign :: SIdentifier -> ModOp -> SExpression -> Interpreter ()
evalAssign n modop e = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (Constant v1, Constant v2) ->
            let res = Constant $ evalModOp modop v1 v2
             in updateBinding n res
        _ -> throwError "Operation not possible"
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

-- TODO too specific, can ONLY swap Integer values by replacing values for each of the keys
evalSwap :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalSwap (n1, _) (n2, _) = if n1 == n2 then return () else 
    gets env >>= \cenv ->
       case (Map.lookup n1 cenv, Map.lookup n2 cenv) of
           (Just v1, Just v2) -> let nenv = Map.adjust (const v1) n2 $ Map.adjust (const v2) n1 cenv
                                  in modify $ \s -> s { env = nenv }

evalConditional :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalConditional e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    if e1' /= Constant 0 -- e1' is True
        then mapM_ evalStatement s1
        else mapM_ evalStatement s2
    e2' <- evalExpression e2
    when (e1' /= e2') $ -- test and assert not equal
        throwError "Entry and exit assertion are not equal"

evalLoop :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalLoop e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    when (e1' /= Constant 0) $ -- e1' is True
        executeLoop s1 s2 e2
    where executeLoop s1 s2 e2 = do
            mapM_ evalStatement s1
            e2' <- evalExpression e2
            when (e2' == Constant 0) $ -- e2' is False
                mapM_ evalStatement s2 >> executeLoop s1 s2 e2

evalLocalBlock :: SIdentifier -> SExpression -> [SStatement] -> SExpression -> Interpreter ()
evalLocalBlock n e1 stmt e2 = do
    e1' <- evalExpression e1
    addBinding n e1'
    mapM_ evalStatement stmt
    n' <- lookupVariableValue n
    e2' <- evalExpression e2
    when (n' /= e2') $
        do varName <- getIdentifierName n
           throwError $
             "Variable '" ++ varName ++
               "' actual value " ++ showValueString n' ++ 
                 " does not match expected value " ++ showValueString e2'

-- evalArrayConstruction :: SExpression -> SIdentifier -> Interpreter ()
-- evalArrayConstruction e n = do
--     e' <- evalExpression e
--     t <- getArrayType n
--     return ()
--     where getArrayType n = gets (symbolTable . saState) >>= \st ->
--             case lookup n st of
--                 Just s -> 
--                     case s of
--                         ClassField t _ _ _ -> return t
--                         _                  -> throwError "Unable to determine array type"
--                 Nothing -> getIdentifierName n >>= \n' -> throwError $ "No array type for " ++ n'

evalStatement :: SStatement -> Interpreter ()
evalStatement (Assign n modop e) = evalAssign n modop e
evalStatement (LocalBlock _ n e1 stmt e2) = evalLocalBlock n e1 stmt e2
evalStatement (Swap t1 t2) = evalSwap t1 t2
evalStatement (Conditional e1 s1 s2 e2) = evalConditional e1 s1 s2 e2
evalStatement (Loop e1 s1 s2 e2) = evalLoop e1 s1 s2 e2
-- evalStatement (LocalCall m args) = evalLocalCall m args
-- evalStatement (ArrayConstruction (_, e) n) = evalArrayConstruction e n
evalStatement Skip = return ()

evalMethod :: SIdentifier -> SProgram -> Interpreter ()
evalMethod mm1 ((_, GMDecl mm2 ps body) : rest)
    | mm1 == mm2 = mapM_ evalStatement body
    | otherwise = evalMethod mm1 rest
evalMethod _ [] = throwError "No matching method identifier"

getProgram :: Interpreter SProgram
getProgram = gets program

getMainMethod :: Interpreter SIdentifier
getMainMethod = gets (mainMethod . saState)

getIdentifierName :: SIdentifier -> Interpreter Identifier
getIdentifierName n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable _ id)   -> return id
        Just (ClassField _ id _ _)  -> return id
        Just (MethodParameter _ id) -> return id
        _ -> throwError $ "Invalid identifier " ++ show n

-- TODO come up with a better way of constructing expression strings (combine with the program inverter?)
showValueString :: SExpression -> String
showValueString (Constant v) = show v
showValueString (Variable n) = show n
showValueString (ArrayElement (v, e)) = show v ++ ", " ++ showValueString e
showValueString Nil = "Nil"
showValueString (Binary bop e1 e2) =
    let e1' = showValueString e1
        e2' = showValueString e2
     in e1' ++ show bop ++ e2'

evalProgram :: Interpreter String
evalProgram = do
    p <- getProgram
    mm <- getMainMethod
    evalMethod mm p
    env <- gets env
    -- TODO fix this mess - not very nice to read, only used for translating identifier integer to variable
    show <$> mapM (\(k, v) -> 
                    getIdentifierName k >>= \k' -> 
                        return (k',v)
                  ) (Map.toList env)

-- interpret :: (SProgram, SAState) -> Except String String
-- interpret (sprg, sastt) = return $ printAST sprg ++ show sastt

interpret :: (SProgram, SAState) -> Except String String
interpret (p, s) = fst <$> runStateT (runInt evalProgram) (initialState p s)
