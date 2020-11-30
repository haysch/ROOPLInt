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
import ClassAnalyzer

type IObject = Maybe Env

data IExpr = Const Integer
           | Object IObject
           | IntegerArray [Integer]
           | ObjectArray [IObject]
           | Nil
    deriving (Show, Eq)

type Loc = SIdentifier
type IExpression = IExpr
type Env = Map SIdentifier Loc
type Store = Map Loc IExpression

data InterpreterState =
    InterpreterState {
        program :: SProgram,
        saState :: SAState,
        env :: Env,
        storeIndex :: SIdentifier,
        store :: Store
    } deriving (Show, Eq)

newtype Interpreter a = Interpreter { runInt :: StateT InterpreterState (Except String) a }
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError String)

initialState :: SProgram -> SAState -> InterpreterState
initialState p s = 
    InterpreterState {
        program = p,
        saState = s,
        env = Map.empty,
        storeIndex = 0,
        store = Map.empty
    }

replaceNth :: Integer -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth p v (x:xs)
    | p == 0  = v:xs
    | otherwise = x:replaceNth (p - 1) v xs

addBinding :: SIdentifier -> IExpression -> Interpreter ()
addBinding n e = do
    cenv <- gets env
    cstore <- gets store
    i <- gets storeIndex
    let nenv = Map.insert n i cenv
        nstore = Map.insert i e cstore
     in modify $ \s -> s { env = nenv, storeIndex = 1 + i, store = nstore }

updateBinding :: SIdentifier -> IExpression -> Interpreter ()
updateBinding n e = do
    env <- gets env
    case Map.lookup n env of
        Just loc -> do
            cstore <- gets store
            let nstore = Map.adjust (const e) loc cstore
             in modify $ \s -> s { store = nstore }
        Nothing -> getIdentifierName n >>= \vn ->
            throwError $ "Unknown reference of variable '" ++ vn ++ "'"

addReference :: (SIdentifier, Maybe SExpression) -> SVariableDeclaration -> Interpreter ()
addReference (n1, Nothing) (GDecl _ n2) = gets env >>= \cenv ->
    case Map.lookup n1 cenv of
        Just l ->
            let nenv = Map.insert n2 l cenv
             in modify $ \s -> s { env = nenv }
        Nothing -> getIdentifierName n1 >>= \vn ->
            throwError $ "Unable to find location for '" ++ vn ++ "'"

removeReference :: SIdentifier -> Interpreter ()
removeReference n = gets env >>= \cenv ->
    let nenv = Map.delete n cenv
     in modify $ \s -> s { env = nenv }

lookupReference :: SIdentifier -> Interpreter IExpression
lookupReference l = gets store >>= \store ->
    case Map.lookup l store of
        Just e -> return e
        Nothing -> throwError $ "Unknown location " ++ show l

lookupVariableTable :: SIdentifier -> Interpreter IExpression
lookupVariableTable n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (ClassField IntegerType _ _ _)         -> return $ Const 0
        Just (ClassField (ObjectType _) _ _ _)      -> return Interpreter.Nil
        Just (ClassField IntegerArrayType _ _ _)    -> 
            getIdentifierName n >>= \vn -> 
                throwError $ "Usage of uninitialized int array '" ++ vn ++ "'"
        Just (ClassField (ObjectArrayType _) _ _ _) -> 
            getIdentifierName n >>= \vn -> 
                throwError $ "Usage of uninitialized object array '" ++ vn ++ "'"
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unknown variable type for " ++ vn

lookupVariableValue :: SIdentifier -> Interpreter IExpression
lookupVariableValue n = gets env >>= \env ->
    case Map.lookup n env of
        Just loc -> lookupReference loc
        Nothing -> lookupVariableTable n >>= \v ->
                       addBinding n v >> return v

checkOutOfBounds :: SIdentifier -> [a] -> Integer -> Interpreter ()
checkOutOfBounds n arr p =
    when (p < 0 || fromIntegral p > (length arr - 1)) $
        getIdentifierName n >>= \vn -> 
            throwError $ "Out of bounds for array '" ++ vn ++ "' at index: " ++ show p

invertModOp :: ModOp -> Interpreter ModOp
invertModOp ModAdd = return ModSub
invertModOp ModSub = return ModAdd
invertModOp ModXor = return ModXor

invertStatement :: SStatement -> Interpreter SStatement
invertStatement (Assign e1 modop e2) = invertModOp modop >>= \modop' -> return $ Assign e1 modop' e2
invertStatement (AssignArrElem e1 modop e2) = invertModOp modop >>= \modop' -> return $ AssignArrElem e1 modop' e2
invertStatement (Swap e1 e2) = return $ Swap e1 e2
invertStatement (Conditional e1 s1 s2 e2) = do
    s1' <- reverse <$> mapM invertStatement s1
    s2' <- reverse <$> mapM invertStatement s2
    return $ Conditional e1 s1' s2' e2
invertStatement (Loop e1 s1 s2 e2) = do
    s1' <- reverse <$> mapM invertStatement s1
    s2' <- reverse <$> mapM invertStatement s2
    return $ Loop e1 s1' s2' e2
invertStatement (ObjectBlock tp n s) = do
    s' <- reverse <$> mapM invertStatement s
    return $ ObjectBlock tp n s'
invertStatement (LocalBlock dt n e1 s e2) = do
    s' <- reverse <$> mapM invertStatement s
    return $ LocalBlock dt n e1 s' e2
invertStatement (LocalCall m args) = return $ LocalUncall m args
invertStatement (LocalUncall m args) = return $ LocalCall m args
invertStatement (ObjectCall o m args) = return $ ObjectUncall o m args
invertStatement (ObjectUncall o m args) = return $ ObjectCall o m args
invertStatement (ObjectConstruction tp n) = return $ ObjectDestruction tp n
invertStatement (ObjectDestruction tp n) = return $ ObjectConstruction tp n
invertStatement Skip = return Skip
invertStatement (CopyReference tp n m) = return $ UnCopyReference tp n m
invertStatement (UnCopyReference tp n m) = return $ CopyReference tp n m
invertStatement (ArrayConstruction tpe n) = return $ ArrayDestruction tpe n
invertStatement (ArrayDestruction tpe n) = return $ ArrayConstruction tpe n

evalBinOp :: BinOp -> SExpression -> SExpression -> Interpreter IExpression
evalBinOp Div e1 e2 = do
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (e1', e2') of
        (Const v1, Const v2) -> if v2 /= 0 then return . Const $ v1 `div` v2
                                                 else throwError "Division by zero"
        _ -> throwError $ "Binary operation '" ++ show e1' ++ " / " ++ show e2' ++ "' not legal"
evalBinOp binop e1 e2 = do
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (e1', e2') of
        (Const v1, Const v2) -> return . Const $ evalOp binop v1 v2
        _ -> throwError $ "Binary operation '" ++ show e1' ++ " " ++ show binop ++ " " ++ show e2' ++ "' not legal"
    where evalOp Add v1 v2      = v1 + v2
          evalOp Sub v1 v2      = v1 - v2
          evalOp Xor v1 v2      = v1 `xor` v2
          evalOp Mul v1 v2      = v1 * v2
          evalOp Mod v1 v2      = v1 `mod` v2
          evalOp BitAnd v1 v2   = v1 .&. v2
          evalOp BitOr v1 v2    = v1 .|. v2
          evalOp And v1 v2      = if v1 == 0 || v2 == 0 then 0 else 1
          evalOp Or v1 v2       = if v1 == 0 && v2 == 0 then 0 else 1
          evalOp Lt v1 v2       = if v1 < v2  then 1 else 0
          evalOp Gt v1 v2       = if v1 > v2  then 1 else 0
          evalOp Eq v1 v2       = if v1 == v2 then 1 else 0
          evalOp Neq v1 v2      = if v1 /= v2 then 1 else 0
          evalOp Lte v1 v2      = if v1 <= v2 then 1 else 0
          evalOp Gte v1 v2      = if v1 >= v2 then 1 else 0

evalExpression :: SExpression -> Interpreter IExpression
evalExpression (Constant n) = return $ Const n
evalExpression (Variable v) = lookupVariableValue v
evalExpression (ArrayElement (_, e)) = evalExpression e
evalExpression AST.Nil = return Interpreter.Nil
evalExpression (Binary binop e1 e2) = evalBinOp binop e1 e2

evalAssign :: SIdentifier -> ModOp -> SExpression -> Interpreter ()
evalAssign n modop e = do
    v <- lookupVariableValue n
    e' <- evalExpression e
    case (v, e') of
        (Const v1, Const v2) ->
            let res = Const $ evalModOp modop v1 v2
             in updateBinding n res
        _ -> throwError "Operation not possible"
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

evalAssignArrElem :: (SIdentifier, SExpression) -> ModOp -> SExpression -> Interpreter ()
evalAssignArrElem (n, e1) modop e2 = do
    v <- lookupVariableValue n
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (v, e1', e2') of
        (IntegerArray ia, Const v1, Const v2) ->
            checkOutOfBounds n ia v1 >>
                let v0 = ia !! fromIntegral v1
                    res = evalModOp modop v0 v2
                    ia' = replaceNth v1 res ia
                 in updateBinding n $ IntegerArray ia'
        _ -> throwError $ "Operation '" ++ show modop ++ "' not possible for '" ++ show v
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

swapArrayValues :: (SIdentifier, IExpression) -> Maybe Integer -> (SIdentifier, IExpression) -> Maybe Integer -> Interpreter ()
swapArrayValues (n1, IntegerArray ia1) (Just p1) (n2, Const v2) Nothing =
    checkOutOfBounds n1 ia1 p1 >>
        let v1 = ia1 !! fromIntegral p1
            ia1' = replaceNth p1 v2 ia1
         in updateBinding n1 (IntegerArray ia1') >> 
                updateBinding n2 (Const v1)
swapArrayValues (n1, Const v1) Nothing (n2, IntegerArray ia2) (Just p2) =
    checkOutOfBounds n2 ia2 p2 >>
        let v2 = ia2 !! fromIntegral p2
            ia2' = replaceNth p2 v1 ia2
         in updateBinding n1 (Const v2) >> 
                updateBinding n2 (IntegerArray ia2')
swapArrayValues (n1, IntegerArray ia1) (Just p1) (n2, IntegerArray ia2) (Just p2) =
    checkOutOfBounds n1 ia1 p1 >> checkOutOfBounds n2 ia2 p2 >>
        let v1 = ia1 !! fromIntegral p1
            v2 = ia2 !! fromIntegral p2
            ia1' = replaceNth p1 v2 ia1
            ia2' = replaceNth p2 v1 ia2
         in updateBinding n1 (IntegerArray ia1') >> 
                updateBinding n2 (IntegerArray ia2')
swapArrayValues (n1, ObjectArray oa1) (Just p1) (n2, Object o2) Nothing =
    checkOutOfBounds n1 oa1 p1 >>
        let o1 = oa1 !! fromIntegral p1
            oa1' = replaceNth p1 o2 oa1
         in updateBinding n1 (ObjectArray oa1') >> 
                updateBinding n2 (Object o1)
swapArrayValues (n1, Object o1) Nothing (n2, ObjectArray oa2) (Just p2) =
    checkOutOfBounds n2 oa2 p2 >>
        let o2 = oa2 !! fromIntegral p2
            oa2' = replaceNth p2 o1 oa2
         in updateBinding n1 (Object o2) >> 
                updateBinding n2 (ObjectArray oa2')
swapArrayValues (n1, ObjectArray oa1) (Just p1) (n2, ObjectArray oa2) (Just p2) =
    checkOutOfBounds n1 oa1 p1 >> checkOutOfBounds n2 oa2 p2 >>
        let o1 = oa1 !! fromIntegral p1
            o2 = oa2 !! fromIntegral p2
            oa1' = replaceNth p1 o2 oa1
            oa2' = replaceNth p2 o1 oa2
         in updateBinding n1 (ObjectArray oa1') >> 
                updateBinding n2 (ObjectArray oa2')

evalSwap :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalSwap s1 s2 = if s1 == s2 then return () else performSwap s1 s2
    where performSwap (n1, m1) (n2, m2) =
            case (m1, m2) of
                (Just e1, Nothing) -> do
                    e1' <- evalExpression e1
                    n1' <- lookupVariableValue n1
                    n2' <- lookupVariableValue n2
                    case e1' of
                        Const p1 -> swapArrayValues (n1, n1') (Just p1) (n2, n2') Nothing
                        _ -> throwError "Unable to find position for swapping"
                (Nothing, Just e2) -> do
                    e2' <- evalExpression e2
                    n1' <- lookupVariableValue n1
                    n2' <- lookupVariableValue n2
                    case e2' of
                        Const p2 -> swapArrayValues (n1, n1') Nothing (n2, n2') (Just p2)
                        _ -> throwError "Unable to find position for swapping"
                (Just e1, Just e2) -> do
                    e1'  <- evalExpression e1
                    e2'  <- evalExpression e2
                    n1' <- lookupVariableValue n1
                    n2' <- lookupVariableValue n2
                    case (e1', e2') of
                        (Const p1, Const p2) -> swapArrayValues (n1, n1') (Just p1) (n2, n2') (Just p2)
                        _ -> throwError "Unable to find position for swapping"
                (Nothing, Nothing) -> 
                    do v1 <- lookupVariableValue n1
                       v2 <- lookupVariableValue n2
                       updateBinding n1 v2 >> updateBinding n2 v1

evalConditional :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalConditional e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    if e1' /= Const 0 -- e1' is True
        then mapM_ evalStatement s1
        else mapM_ evalStatement s2
    e2' <- evalExpression e2
    when (e1' /= e2') $ -- test and assert not equal
        throwError "Entry and exit assertion are not equal"

evalLoop :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalLoop e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    when (e1' /= Const 0) $ -- e1' is True
        executeLoop s1 s2 e2
    where executeLoop s1 s2 e2 = do
            mapM_ evalStatement s1
            e2' <- evalExpression e2
            when (e2' == Const 0) $ -- e2' is False
                mapM_ evalStatement s2 >> executeLoop s1 s2 e2

evalObjectBlock :: SIdentifier -> [SStatement] -> Interpreter ()
evalObjectBlock n stmt =
    evalObjectConstruction (n, Nothing) >>
        mapM_ evalStatement stmt >>
            evalObjectDestruction (n, Nothing) >>
                removeReference n

evalLocalBlock :: SIdentifier -> SExpression -> [SStatement] -> SExpression -> Interpreter ()
evalLocalBlock n e1 stmt e2 = do
    e1' <- evalExpression e1
    addBinding n e1'
    mapM_ evalStatement stmt
    v <- lookupVariableValue n
    e2' <- evalExpression e2
    if v == e2' then 
        removeReference n -- ??
    else 
        getIdentifierName n >>= \vn ->
           throwError $
             "Variable '" ++ vn ++
               "' actual value " ++ showValueString v ++ 
                 " does not match expected value " ++ showValueString e2'

evalCall :: [(SIdentifier, Maybe SExpression)] -> [SVariableDeclaration] -> [SStatement] -> Interpreter ()
evalCall args ps stmt =
    zipWithM_ addReference args ps >> -- add references to environment
        mapM_ evalStatement stmt >>
            mapM_ (\(GDecl _ p) -> removeReference p) ps -- remove references from environment

evalLocalCall :: SIdentifier -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalLocalCall m args = do
    (ps, stmt) <- getMethod m
    evalCall args ps stmt

evalLocalUncall :: SIdentifier -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalLocalUncall m args = do
    (ps, stmt) <- getMethod m
    stmt' <- reverse <$> mapM invertStatement stmt
    evalCall args ps stmt'

evalObjectConstruction :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectConstruction (n, Nothing) = 
    let obj = Object $ Just Map.empty
     in addBinding n obj
evalObjectConstruction (n, Just e) = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) ->
            checkOutOfBounds n oa p >>
                let o = Just Map.empty
                    oa' = replaceNth p o oa
                 in updateBinding n $ ObjectArray oa'

evalObjectDestruction :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectDestruction (n, Nothing) = updateBinding n Interpreter.Nil
evalObjectDestruction (n, Just e) = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) -> 
            checkOutOfBounds n oa p >>
                let oa' = replaceNth p Nothing oa
                 in updateBinding n $ ObjectArray oa'
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to destruction " ++ vn

evalCopyReference :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalCopyReference n m = return ()

evalUnCopyReference :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalUnCopyReference (n, _) = return ()

evalArrayConstruction :: SExpression -> SIdentifier -> Interpreter ()
evalArrayConstruction e n = do
    e' <- evalExpression e
    t <- getArrayType n
    case (t, e') of
        (IntegerArrayType, Const l)  -> addBinding n (IntegerArray $ replicate (fromIntegral l) 0)
        (ObjectArrayType _, Const l) -> addBinding n (ObjectArray $ replicate (fromIntegral l) Nothing)
        _ -> throwError $ "Unsupported array datatype " ++ show t
    where getArrayType n = gets (symbolTable . saState) >>= \st ->
            case lookup n st of
                Just (LocalVariable tp _) -> return tp
                Just (ClassField tp _ _ _) -> return tp
                Just (MethodParameter tp _) -> return tp
                Nothing -> getIdentifierName n >>= \n' -> throwError $ "No array type for " ++ n'

evalArrayDeconstruction :: SIdentifier -> Interpreter ()
evalArrayDeconstruction n = updateBinding n Interpreter.Nil

evalStatement :: SStatement -> Interpreter ()
evalStatement (Assign n modop e) = evalAssign n modop e
evalStatement (AssignArrElem (n, e1) modop e2) = evalAssignArrElem (n, e1) modop e2
evalStatement (Swap t1 t2) = evalSwap t1 t2
evalStatement (Conditional e1 s1 s2 e2) = evalConditional e1 s1 s2 e2
evalStatement (Loop e1 s1 s2 e2) = evalLoop e1 s1 s2 e2
evalStatement (ObjectBlock _ n stmt) = evalObjectBlock n stmt
evalStatement (LocalBlock _ n e1 stmt e2) = evalLocalBlock n e1 stmt e2
evalStatement (LocalCall m args) = evalLocalCall m args
evalStatement (LocalUncall m args) = evalLocalUncall m args
evalStatement (ObjectConstruction _ (n, e)) = evalObjectConstruction (n, e)
evalStatement (ObjectDestruction _ (n, e)) = evalObjectDestruction (n, e)
-- evalStatement (CopyReference _ n m) = evalCopyReference n m
-- evalStatement (UnCopyReference _ n _) = evalUnCopyReference n
evalStatement (ArrayConstruction (_, e) n) = evalArrayConstruction e n
evalStatement (ArrayDestruction _ n) = evalArrayDeconstruction n
evalStatement Skip = return ()

evalMainMethod :: SIdentifier -> SProgram -> Interpreter ()
evalMainMethod mm1 ((_, GMDecl mm2 _ body) : rest)
    | mm1 == mm2 = mapM_ evalStatement body
    | otherwise = evalMainMethod mm1 rest
evalMainMethod _ [] = throwError "No main method found"

getObjectType :: SIdentifier -> Interpreter TypeName
getObjectType n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable (ObjectType tp) _) -> return tp
        Just (ClassField (ObjectType tp) _ _ _) -> return tp
        Just (MethodParameter (ObjectType tp) _) -> return tp
        Just (LocalVariable (ObjectArrayType tp) _) -> return tp
        Just (ClassField (ObjectArrayType tp) _ _ _) -> return tp
        Just (MethodParameter (ObjectArrayType tp) _) -> return tp
        Nothing -> getIdentifierName n >>= \vn ->
            throwError $ "Unable to determine object type for " ++ vn

getFields :: TypeName -> Interpreter [VariableDeclaration]
getFields tn = do
    cs <- gets (classes . caState . saState)
    case lookup tn cs of
        Just (GCDecl _ _ fs _) -> return fs
        Nothing -> throwError $ "Unknown class '" ++ tn ++ "'"

getProgram :: Interpreter SProgram
getProgram = gets program

getMainMethod :: Interpreter SIdentifier
getMainMethod = gets (mainMethod . saState)

getMethod :: SIdentifier -> Interpreter ([SVariableDeclaration], [SStatement])
getMethod m = do
    prog <- gets program
    case findMethod prog m of
        Just mt -> return mt
        Nothing -> throwError $ "Unable to find method " ++ show m
    where findMethod [] _     = Nothing
          findMethod ((_, GMDecl i ps stmt):prgs) m
            | i == m = Just (ps, stmt)
            | otherwise = findMethod prgs m

getIdentifierName :: SIdentifier -> Interpreter Identifier
getIdentifierName n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable _ id)   -> return id
        Just (ClassField _ id _ _)  -> return id
        Just (MethodParameter _ id) -> return id
        _ -> throwError $ "Invalid identifier " ++ show n

-- TODO come up with a better way of constructing expression strings (combine with the program inverter?)
showValueString :: IExpression -> String
showValueString (Const v) = show v
-- showValueString (Variable n) = show n
-- showValueString (ArrayElement (v, e)) = show v ++ ", " ++ showValueString e
-- showValueString AST.Nil = "Nil"
-- showValueString (Binary bop e1 e2) =
--     let e1' = showValueString e1
--         e2' = showValueString e2
--      in e1' ++ show bop ++ e2'

evalProgram :: Interpreter String
evalProgram = do
    p <- getProgram
    mm <- getMainMethod
    evalMainMethod mm p
    env <- gets env
    -- TODO fix this mess - not very nice to read, only used for translating identifier integer to variable
    show <$> mapM (\(k, l) -> 
                    getIdentifierName k >>= \k' ->
                        lookupReference l >>= \v ->
                            return (k',v)
                  ) (Map.toList env)

-- interpret :: (SProgram, SAState) -> Except String String
-- interpret (sprg, sastt) = return $ printAST sprg ++ printAST sastt

interpret :: (SProgram, SAState) -> Except String String
interpret (p, s) = fst <$> runStateT (runInt evalProgram) (initialState p s) -- printAST . snd <$> -- for printing state
