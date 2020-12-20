{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Interpreter (interpret) where

import Control.Monad.Except

import qualified Data.Map as Map
import Data.Bits

import AST
import ScopeAnalyzer
import Control.Monad.State

import Debug.Trace (trace, traceShow)
import ClassAnalyzer
import Data.List

data InterpreterState =
    InterpreterState {
        program :: SProgram,
        saState :: SAState,
        caller :: Env,
        objectScope :: ObjectScope,
        referenceScope :: ReferenceScope,
        store :: Store,
        storeIndex :: SIdentifier,
        invCache :: [(SIdentifier, [SStatement])]
    } deriving (Show, Eq)

newtype Interpreter a = Interpreter { runInt :: StateT InterpreterState (Except String) a }
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError String)

-- | Creating the initial interpreter state
initialState :: SProgram -> SAState -> InterpreterState
initialState p s = 
    InterpreterState {
        program = p,
        saState = s,
        caller = Map.empty,
        objectScope = [],
        referenceScope = [],
        store = Map.empty,
        storeIndex = 0,
        invCache = []
    }

-- | Replaces the n'th entry in a list
replaceNth :: Integer -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth p v (x:xs)
    | p == 0  = v:xs
    | otherwise = x:replaceNth (p - 1) v xs

-- | Returns the current object scope
topObjectScope :: Interpreter Env
topObjectScope = gets objectScope >>= 
    \case
        (e:_) -> return e
        [] -> throwError "Empty object scope stack"

-- | Returns the current reference scope
topReferenceScope :: Interpreter Ref
topReferenceScope = gets referenceScope >>=
    \case
        (r:_) -> return r
        [] -> throwError "Empty reference scope stack"

-- | Enters a new object scope using an object's environment as reference and sets caller to the calling object's environment, if any exists
enterObjectScope :: Env -> Interpreter ()
enterObjectScope env = gets objectScope >>= \os ->
    let clr = case os of
                (o:_) -> o
                [] -> Map.empty
     in modify $ \s -> s { caller = clr, objectScope = env : objectScope s, referenceScope = Map.empty : referenceScope s }

-- | Leaves the current object scope and returns its updated environment
leaveObjectScope :: Interpreter Env
leaveObjectScope = do
    curr <- topObjectScope
    modify $ \s -> s { caller = Map.empty, objectScope = drop 1 (objectScope s), referenceScope = drop 1 (referenceScope s) }
    return curr

-- | Creates an object by entering a new scope and initializing classfields. Returns the generated object environment.
createObject :: TypeName -> Interpreter Env
createObject tn = do
    fs <- getFields tn
    enterObjectScope Map.empty
    initializeObject tn fs
    leaveObjectScope

-- | Adds variable binding to store and maps the reference to the current object environment
addObjectBinding :: SIdentifier -> IExpression -> Interpreter ()
addObjectBinding n e = do
    os <- topObjectScope
    store <- gets store
    storeIdx <- gets storeIndex
    let os' = Map.insert n storeIdx os
        store' = Map.insert storeIdx e store
     in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), store = store', storeIndex = 1 + storeIdx }

-- | Fetches the binding location of an identifier
getBindingLocation :: SIdentifier -> Interpreter Location
getBindingLocation n = topObjectScope >>= \os ->
    case Map.lookup n os of
        Just b -> return b
        Nothing -> getIdentifierName n >>= \vn ->
            throwError $ "Unknown reference of variable '" ++ vn ++ "'"

-- | Updates a variable binding in the store
updateBinding :: SIdentifier -> IExpression -> Interpreter ()
updateBinding n e = getBindingLocation n >>= \l -> updateStore l e

-- | Updates a store binding
updateStore :: Location -> IExpression -> Interpreter ()
updateStore l e = do
    store <- gets store
    let store' = Map.adjust (const e) l store
     in modify $ \s -> s { store = store' }

-- | Adds a variable reference to the environment
addReference :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
addReference (n1, Nothing) (n2, Nothing) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- gets caller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just l ->
            let os' = Map.insert n2 l os
                rs' = Map.insert n2 n1 rs
             in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ "Unable to find location for '" ++ vn ++ "'"
addReference (n1, Just p1) (n2, Nothing) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- gets caller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just l -> lookupStore l >>= \e1 ->
            let os' = case (e1, p1) of
                        (IntegerArray ia, Constant p1') ->
                            let il = ia !! fromIntegral p1'
                             in Map.insert n2 il os
                        (ObjectArray oa, Constant p') ->
                            let ol = oa !! fromIntegral p'
                             in Map.insert n2 ol os
                rs' = Map.insert n2 n1 rs -- TODO: Add offset?
             in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ "Unable to find location for '" ++ vn ++ "'"
addReference (n1, Nothing) (n2, Just p2) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- gets caller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just l -> lookupVariableValue n2 >>= \e2 ->
            case (e2, p2) of
                (IntegerArray ia, Constant p2') ->
                    let ia' = replaceNth p2' l ia
                     in updateBinding n2 $ IntegerArray ia'
                (ObjectArray oa, Constant p2') ->
                    let oa' = replaceNth p2' l oa
                     in updateBinding n2 $ ObjectArray oa'
            >> 
            let rs' = Map.insert n2 n1 rs -- TODO: Add offset?
             in modify $ \s -> s { referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ "Unable to find location for '" ++ vn ++ "'"
addReference (n1, Just p1) (n2, Just p2) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- gets caller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just _ -> do
            e1 <- lookupVariableValue n1
            e2 <- lookupVariableValue n2
            case (e1, p1, e2, p2) of
                (IntegerArray ia1, Constant p1', IntegerArray ia2, Constant p2') ->
                    let il1 = ia1 !! fromIntegral p1'
                        ia2' = replaceNth p2' il1 ia2
                     in updateBinding n2 $ IntegerArray ia2'
                (ObjectArray oa1, Constant p1', ObjectArray oa2, Constant p2') ->
                    let ol1 = oa1 !! fromIntegral p1'
                        oa2' = replaceNth p2' ol1 oa2
                     in updateBinding n2 $ ObjectArray oa2'
            >> 
            let rs' = Map.insert n2 n1 rs -- TODO: Add offset?
             in modify $ \s -> s { referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ "Unable to find location for '" ++ vn ++ "'"

-- | Removes a variable reference from the environment
removeReference :: SIdentifier -> Interpreter ()
removeReference n = do
    os <- topObjectScope
    rs <- topReferenceScope
    let os' = Map.delete n os
        rs' = Map.delete n rs
     in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), referenceScope = rs' : drop 1 (referenceScope s) }

-- | Adds expression to store and returns its location. Internal method for bypassing creation of variables
addToStore :: IExpression -> Interpreter SIdentifier
addToStore e = do
    store <- gets store
    storeIdx <- gets storeIndex
    let store' = Map.insert storeIdx e store
     in modify $ \s -> s { store = store', storeIndex = 1 + storeIdx } 
    return storeIdx

-- | Looks up location in store to get the value
lookupStore :: SIdentifier -> Interpreter IExpression
lookupStore l = gets store >>= \store ->
    case Map.lookup l store of
        Just e -> return e
        Nothing -> throwError $ "Unknown location " ++ show l

-- | Looks up a reference in the environment to find value in store
lookupVariableValue :: SIdentifier -> Interpreter IExpression
lookupVariableValue n = topObjectScope >>= \os ->
    case Map.lookup n os of
        Just loc -> lookupStore loc >>= \e' ->
            return e'
        Nothing -> getIdentifierName n >>= \vn -> 
            throwError $ "Variable '" ++ vn ++ "' has not been defined"

-- | Checks whether an array index is out of bounds
checkOutOfBounds :: SIdentifier -> [a] -> Integer -> Interpreter ()
checkOutOfBounds n arr p =
    when (p < 0 || fromIntegral p > (length arr - 1)) $
        getIdentifierName n >>= \vn -> 
            throwError $ "Out of bounds for array '" ++ vn ++ "' at index: " ++ show p

-- | Inverts the Mod operator
invertModOp :: ModOp -> Interpreter ModOp
invertModOp ModAdd = return ModSub
invertModOp ModSub = return ModAdd
invertModOp ModXor = return ModXor

-- | Inverts a scoped statement
invertStatement :: SStatement -> Interpreter SStatement
invertStatement (Assign e1 modop e2) = invertModOp modop >>= \modop' -> return $ Assign e1 modop' e2
invertStatement (AssignArrElem e1 modop e2) = invertModOp modop >>= \modop' -> return $ AssignArrElem e1 modop' e2
invertStatement (Swap e1 e2) = return $ Swap e1 e2
invertStatement (Conditional e1 s1 s2 e2) = do
    s1' <- reverse <$> mapM invertStatement s1
    s2' <- reverse <$> mapM invertStatement s2
    return $ Conditional e2 s1' s2' e1
invertStatement (Loop e1 s1 s2 e2) = do
    s1' <- reverse <$> mapM invertStatement s1
    s2' <- reverse <$> mapM invertStatement s2
    return $ Loop e2 s1' s2' e1
invertStatement (ObjectBlock tp n s) = do
    s' <- reverse <$> mapM invertStatement s
    return $ ObjectBlock tp n s'
invertStatement (LocalBlock dt n e1 s e2) = do
    s' <- reverse <$> mapM invertStatement s
    return $ LocalBlock dt n e2 s' e1
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

invertStatements :: SIdentifier -> [SStatement] -> Interpreter [SStatement]
invertStatements i stmt = gets invCache >>= \iv ->
    case lookup i iv of
        Just stmt' -> return stmt'
        Nothing -> do 
            stmt' <- reverse <$> mapM invertStatement stmt
            insertInverseStatement i stmt'
            return stmt'
    where insertInverseStatement :: SIdentifier -> [SStatement] -> Interpreter ()
          insertInverseStatement i stmt = modify $ \s -> s { invCache = (i, stmt) : invCache s}

-- | Evaluates a binary expression to a interpreted expression
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
        (Null, Const _) -> return $ Const 0
        (Null, Null) -> return . Const $ evalOp binop 1 1
        (Object _ _, Null) -> return . Const $ evalOp binop 1 0
        (Null, Object _ _) -> return . Const $ evalOp binop 0 1
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

-- | Evaluates a scoped expression to an interpreted expression
evalExpression :: SExpression -> Interpreter IExpression
evalExpression (Constant n) = return $ Const n
evalExpression (Variable v) = lookupVariableValue v
evalExpression (ArrayElement (v, e)) = do
    v' <- lookupVariableValue v
    e' <- evalExpression e
    case (v', e') of
        (IntegerArray ia, Const p) ->
            checkOutOfBounds v ia p >>
                let vl = ia !! fromIntegral p
                 in lookupStore vl >>=
                     \case
                        Const v -> return $ Const v
                        err -> showValueString [] err >>= \err' ->
                            throwError $ "Location points to non-integer: " ++ err'
        (ObjectArray oa, Const p) ->
            checkOutOfBounds v oa p >>
                let ol = oa !! fromIntegral p
                 in lookupStore ol >>=
                    \case
                        Object tn o -> return $ Object tn o
                        err -> showValueString [] err >>= \err' ->
                                throwError $ "Location points to non-object: " ++ err'
        _ -> getIdentifierName v >>= \vn ->
            throwError $ "Unable to find array '" ++ vn ++ "'"
evalExpression AST.Nil = return Null
evalExpression (Binary binop e1 e2) = evalBinOp binop e1 e2

-- | Evaluates a variable assignment of a scoped expression
evalAssign :: SIdentifier -> ModOp -> SExpression -> Interpreter ()
evalAssign n modop e = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (Const v1, Const v2) ->
            let res = Const $ evalModOp modop v1 v2
             in updateBinding n res
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Operation '" ++ show modop ++ "' not possible for '" ++ vn ++ "' with '" ++ show e' ++ "'"
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

-- | Evaluates an array index assignment of a scoped expression
evalAssignArrElem :: (SIdentifier, SExpression) -> ModOp -> SExpression -> Interpreter ()
evalAssignArrElem (n, e1) modop e2 = do
    n' <- lookupVariableValue n
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (n', e1', e2') of
        (IntegerArray ia, Const p, Const v2) ->
            checkOutOfBounds n ia p >>
                let vl = ia !! fromIntegral p
                 in lookupStore vl >>= 
                     \case 
                        Const v1 -> updateStore vl $ Const (evalModOp modop v1 v2)
                        _ -> getIdentifierName n >>= \vn ->
                            throwError $ "Unable to perform array assignment for '" ++ vn ++ "[" ++ show p ++ "]'"
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Operation '" ++ show modop ++ "' not possible for '" ++ vn ++ "'"
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

-- | Evaluates a swap between values in arrays and variables, and arrays to arrays
swapArrayValues :: (SIdentifier, IExpression) -> Maybe Integer -> (SIdentifier, IExpression) -> Maybe Integer -> Interpreter ()
swapArrayValues (n1, IntegerArray ia1) (Just p1) (n2, Const _) Nothing =
    checkOutOfBounds n1 ia1 p1 >>
        getBindingLocation n2 >>= \l2 ->
            let vl1 = ia1 !! fromIntegral p1
                ia1' = replaceNth p1 l2 ia1
            in lookupStore vl1 >>=
                \case
                    Const _ -> 
                        updateBinding n1 (IntegerArray ia1') >> 
                            updateLocation n2 vl1
                    _ -> throwSwapValueMismatch (n1, Just p1) (n2, Nothing) "integer"
swapArrayValues (n1, Const _) Nothing (n2, IntegerArray ia2) (Just p2) =
    checkOutOfBounds n2 ia2 p2 >>
        getBindingLocation n1 >>= \l1 ->
            let vl2 = ia2 !! fromIntegral p2
                ia2' = replaceNth p2 l1 ia2
            in lookupStore vl2 >>=
                \case
                    Const _ -> 
                        updateLocation n1 vl2 >>
                            updateBinding n2 (IntegerArray ia2')
                    _ -> throwSwapValueMismatch (n1, Nothing) (n2, Just p2) "integer"
swapArrayValues (n1, IntegerArray ia1) (Just p1) (n2, IntegerArray ia2) (Just p2) =
    checkOutOfBounds n1 ia1 p1 >> checkOutOfBounds n2 ia2 p2 >>
        let vl1 = ia1 !! fromIntegral p1
            vl2 = ia2 !! fromIntegral p2
            ia1' = replaceNth p1 vl2 ia1
            ia2' = replaceNth p2 vl1 ia2
         in do
            v1 <- lookupStore vl1
            v2 <- lookupStore vl2
            case (v1, v2) of 
                (Const _, Const _) -> updateBinding n1 (IntegerArray ia1') >> 
                    updateBinding n2 (IntegerArray ia2')
                _ -> throwSwapValueMismatch (n1, Just p1) (n2, Just p2) "integer"
swapArrayValues (n1, ObjectArray oa1) (Just p1) (n2, Object tn2 _) Nothing =
    checkOutOfBounds n1 oa1 p1 >> do
        l2 <- getBindingLocation n2
        let ol1 = oa1 !! fromIntegral p1
            oa1' = replaceNth p1 l2 oa1
         in lookupStore ol1 >>= 
             \case 
                (Object tn1 _) -> assertObjectTypes (tn1, n1) (tn2, n2) >>
                    updateBinding n1 (ObjectArray oa1') >> updateLocation n2 ol1
                _ -> throwSwapValueMismatch (n1, Just p1) (n2, Nothing) "object"
swapArrayValues (n1, Object tn1 _) Nothing (n2, ObjectArray oa2) (Just p2) =
    checkOutOfBounds n1 oa2 p2 >> do
        l1 <- getBindingLocation n1
        let ol2 = oa2 !! fromIntegral p2
            oa2' = replaceNth p2 l1 oa2
         in lookupStore ol2 >>= 
             \case 
                (Object tn2 _) -> assertObjectTypes (tn1, n1) (tn2, n2) >>
                    updateLocation n1 ol2 >> updateBinding n2 (ObjectArray oa2')
                _ -> throwSwapValueMismatch (n1, Nothing) (n2, Just p2) "object"
swapArrayValues (n1, ObjectArray oa1) (Just p1) (n2, ObjectArray oa2) (Just p2) =
    checkOutOfBounds n1 oa1 p1 >> checkOutOfBounds n2 oa2 p2 >>
        let ol1 = oa1 !! fromIntegral p1
            ol2 = oa2 !! fromIntegral p2
            oa1' = replaceNth p1 ol2 oa1
            oa2' = replaceNth p2 ol1 oa2
         in do
            o1 <- lookupStore ol1
            o2 <- lookupStore ol2
            case (o1, o2) of
                (Object tn1 _, Object tn2 _) -> assertObjectTypes (tn1, n1) (tn2, n2) >>
                    updateBinding n1 (ObjectArray oa1') >> updateBinding n2 (ObjectArray oa2')
                _ -> throwSwapValueMismatch (n1, Just p1) (n2, Just p2) "object"
swapArrayValues (n1, _) _ (n2, _) _ = do
    vn1 <- getIdentifierName n1
    vn2 <- getIdentifierName n2
    throwError $ "Unable to swap references between '" ++ vn1 ++ "' and '" ++ vn2 ++ "'"

-- | Runtime error: Throws an error stating that the value types of the swapping location does not match
throwSwapValueMismatch :: (SIdentifier, Maybe Integer) -> (SIdentifier, Maybe Integer) -> String -> Interpreter ()
throwSwapValueMismatch (n1, Nothing) (n2, Just p2) t = do
    vn1 <- getIdentifierName n1
    vn2 <- getIdentifierName n2
    throwError $ "Trying to swap between " ++ t ++ " and non-" ++ t ++ " in '" ++ 
        vn1 ++ " <=> " ++ vn2 ++ "[" ++ show p2 ++ "]'"
throwSwapValueMismatch (n1, Just p1) (n2, Nothing) t = do
    vn1 <- getIdentifierName n1
    vn2 <- getIdentifierName n2
    throwError $ "Trying to swap between " ++ t ++ " and non-" ++ t ++ " in '" ++ 
        vn1 ++ "[" ++ show p1 ++ "] <=> " ++ vn2 ++ "'"
throwSwapValueMismatch (n1, Just p1) (n2, Just p2) t = do
    vn1 <- getIdentifierName n1
    vn2 <- getIdentifierName n2
    throwError $ "Trying to swap between " ++ t ++ " and non-" ++ t ++ " in '" ++ 
        vn1 ++ "[" ++ show p1 ++ "] <=> " ++ vn2 ++ "[" ++ show p2 ++ "]'"

-- | Asserts that the types used for swapping are equal
assertObjectTypes :: (TypeName, SIdentifier) -> (TypeName, SIdentifier) -> Interpreter ()
assertObjectTypes (tn1, n1) (tn2, n2) =
    when (tn1 /= tn2) $ do 
        vn1 <- getIdentifierName n1
        vn2 <- getIdentifierName n2
        throwError $ "Mismatch between variable types of '" ++ vn1 ++ "' and '" ++ vn2 ++ "'\n" ++
            "Types '" ++ tn1 ++ "' and '" ++ tn2 ++ "'"

-- | Evaluates a swap between variables
evalSwap :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalSwap s1 s2 = if s1 == s2 then return () else performSwap s1 s2
    where performSwap (n1, Just e1) (n2, Nothing) = do
            e1' <- evalExpression e1
            n1' <- lookupVariableValue n1
            n2' <- lookupVariableValue n2
            case e1' of
                Const p1 -> swapArrayValues (n1, n1') (Just p1) (n2, n2') Nothing
                _ -> getIdentifierName n1 >>= \vn1 ->
                    throwError $ "Unable to find array index for swapping in '" ++ vn1 ++ "'"
          performSwap (n1, Nothing) (n2, Just e2) = do
            e2' <- evalExpression e2
            n1' <- lookupVariableValue n1
            n2' <- lookupVariableValue n2
            case e2' of
                Const p2 -> swapArrayValues (n1, n1') Nothing (n2, n2') (Just p2)
                _ -> getIdentifierName n2 >>= \vn ->
                        throwError $ "Unable to find array index for swapping in '" ++ vn ++ "'"
          performSwap (n1, Just e1) (n2, Just e2) = do
            e1'  <- evalExpression e1
            e2'  <- evalExpression e2
            n1' <- lookupVariableValue n1
            n2' <- lookupVariableValue n2
            case (e1', e2') of
                (Const p1, Const p2) -> swapArrayValues (n1, n1') (Just p1) (n2, n2') (Just p2)
                (_, Const _) -> getIdentifierName n1 >>= \vn1 ->
                    throwError $ "Unable to find array index for swapping in '" ++ vn1 ++ "'"
                (Const _, _) -> getIdentifierName n2 >>= \vn2 ->
                    throwError $ "Unable to find array index for swapping in '" ++ vn2 ++ "'"
                _ -> do
                    vn1 <- getIdentifierName n1
                    vn2 <- getIdentifierName n2
                    throwError $ "Unable to find array index for swapping in '" ++ vn1 ++ "' and '" ++ vn2 ++ "'"
          performSwap (n1, Nothing) (n2, Nothing) = do
            l1 <- getBindingLocation n1
            l2 <- getBindingLocation n2
            updateLocation n1 l2 >> updateLocation n2 l1

-- | Updates every reference to a store location in the objectscope list
updateLocation :: SIdentifier -> Location -> Interpreter ()
updateLocation n l = do
    os <- gets objectScope
    rs <- gets referenceScope
    let os' = updateObjectScopeLoc n l os rs
     in modify $ \s -> s { objectScope = os' }

    where updateObjectScopeLoc :: SIdentifier -> Location -> ObjectScope -> ReferenceScope -> ObjectScope
          updateObjectScopeLoc n l (o:ostack) (r:rstack) = 
              let os' = Map.adjust (const l) n o
               in case Map.lookup n r of
                    Just n' -> os' : updateObjectScopeLoc n' l ostack rstack
                    Nothing -> os' : ostack

-- | Evaluates a conditional statement with entry and exit assertion
evalConditional :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalConditional e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    if e1' /= Const 0 -- e1' is True
        then mapM_ evalStatement s1
        else mapM_ evalStatement s2
    e2' <- evalExpression e2
    when (e1' /= e2') $ -- test and assert not equal
        throwError $ "Exit assertion does not match entry. Should be " ++ show (isTrue e1')
    where isTrue (Const 0) = False
          isTrue (Const _) = True
          isTrue _ = error "Input is not a valid boolean value"

-- | Evaluates a loop statement
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

-- | Evaluates an object block with object construction and destruction
evalObjectBlock :: TypeName -> SIdentifier -> [SStatement] -> Interpreter ()
evalObjectBlock tn n stmt =
    evalObjectConstruction tn (n, Nothing) >>
        mapM_ evalStatement stmt >>
            evalObjectDestruction (n, Nothing) >>
                removeReference n

-- | Evaluates a local block with exit assertion
evalLocalBlock :: SIdentifier -> SExpression -> [SStatement] -> SExpression -> Interpreter ()
evalLocalBlock n e1 stmt e2 = do
    e1' <- evalExpression e1
    addObjectBinding n e1'
    mapM_ evalStatement stmt
    e1' <- lookupVariableValue n
    e2' <- evalExpression e2
    if e1' == e2' then 
        removeReference n
    else 
        getIdentifierName n >>= \vn ->
            showValueString [] e1' >>= \v1 ->
                showValueString [] e2' >>= \v2 ->
                    throwError $
                        "Variable '" ++ vn ++
                        "' actual value " ++ v1 ++ 
                            " does not match expected value " ++ v2

-- | Evaluation of method calling
evalCall :: [(SIdentifier, Maybe SExpression)] -> [SVariableDeclaration] -> [SStatement] -> Interpreter ()
evalCall args ps stmt =
    let ps' = map (\(GDecl _ p) -> (p, Nothing)) ps
     in zipWithM_ addReference args ps' >> -- add references to environment
            mapM_ evalStatement stmt >>
                mapM_ (\(GDecl _ p) -> removeReference p) ps -- remove references from environment

-- | Evaluation of a calling a local method
evalLocalCall :: SIdentifier -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalLocalCall m args = do
    (ps, stmt) <- getMethod m
    evalCall args ps stmt

-- | Evaluation of uncalling a local method
evalLocalUncall :: SIdentifier -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalLocalUncall m args = do
    (ps, stmt) <- getMethod m
    stmt' <- invertStatements m stmt
    evalCall args ps stmt'

-- | Evaluation of calling an object method
evalObjectCall :: (SIdentifier, Maybe SExpression) -> MethodName -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalObjectCall (n, Nothing) m args = lookupVariableValue n >>=
    \case
        Object tn oenv -> do
            enterObjectScope oenv
            (_, ps, stmt) <- getObjectMethod tn m
            evalCall args ps stmt
            oenv' <- leaveObjectScope
            addObjectBinding n $ Object tn oenv'
        Null -> getIdentifierName n >>= \vn ->
            throwError $ "Calling object '" ++ show (vn, n) ++ "::" ++ m ++ "'. Object has not been initialized"
        _ -> getIdentifierName n >>= \vn ->
            throwError $ "Unable to call object '" ++ vn ++ "'"
evalObjectCall (n, Just e) m args = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) -> 
            checkOutOfBounds n oa p >>
                let ol = oa !! fromIntegral p
                 in lookupStore ol >>= 
                    \case
                        Object tn oenv -> do
                            enterObjectScope oenv
                            (_, ps, stmt) <- getObjectMethod tn m
                            evalCall args ps stmt
                            oenv' <- leaveObjectScope
                            updateStore ol $ Object tn oenv'
                        Null -> getIdentifierName n >>= \vn ->
                            throwError $ "Calling object '" ++ show (vn, n) ++ "::" ++ m ++ "'. Object has not been initialized"
                        _ -> getIdentifierName n >>= \vn ->
                                throwError $ "Unable to call object '" ++ vn ++ "' at index " ++ show p
        _ -> getIdentifierName n >>= \vn ->
            throwError $ "Unable to find object to call in '" ++ vn ++ "'"

-- | Evaluation of uncalling an object method
evalObjectUncall :: (SIdentifier, Maybe SExpression) -> MethodName -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalObjectUncall (n, Nothing) m args = lookupVariableValue n >>=
    \case
        Object tn oenv -> do
            enterObjectScope oenv
            (i, ps, stmt) <- getObjectMethod tn m
            stmt' <- invertStatements i stmt
            evalCall args ps stmt'
            oenv' <- leaveObjectScope
            addObjectBinding n $ Object tn oenv'
        Null -> 
            getIdentifierName n >>= \vn ->
                throwError $ "Uncalling object '" ++ show (vn, n) ++ "::" ++ m ++ "'. Object has not been initialized"
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to uncall object '" ++ vn ++ "'"
evalObjectUncall (n, Just e) m args = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) -> 
            checkOutOfBounds n oa p >>
                let ol = oa !! fromIntegral p
                 in lookupStore ol >>=
                    \case 
                        Object tn oenv -> do
                            enterObjectScope oenv
                            (i, ps, stmt) <- getObjectMethod tn m
                            stmt' <- invertStatements i stmt
                            evalCall args ps stmt'
                            oenv' <- leaveObjectScope
                            updateStore ol $ Object tn oenv'
                        Null -> 
                            getIdentifierName n >>= \vn ->
                                throwError $ "Uncalling object '" ++ show (vn, n) ++ "::" ++ m ++ "'. Object has not been initialized"
                        _ -> getIdentifierName n >>= \vn ->
                                throwError $ "Unable to uncall object '" ++ vn ++ "' at index " ++ show p
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to uncall object '" ++ vn ++ "'"

-- | Evaluation of constructing an object
evalObjectConstruction :: TypeName -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectConstruction tn (n, Nothing) = do
    o <- createObject tn
    let obj = Object tn o
     in addObjectBinding n obj
evalObjectConstruction tn (n, Just e) = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) ->
            checkOutOfBounds n oa p >>
                createObject tn >>= \o -> 
                    let ol = oa !! fromIntegral p
                     in updateStore ol (Object tn o)
        (_, Const p) -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to construct '" ++ vn ++ "[" ++ show p ++ "]'. Variable is not an object array."
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to construct '" ++ vn ++ "'. Variable is not an object array."

-- | Evaluation of destructing an object
evalObjectDestruction :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectDestruction (n, Nothing) = addObjectBinding n Null
evalObjectDestruction (n, Just e) = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) -> 
            checkOutOfBounds n oa p >>
                let ol = oa !! fromIntegral p
                 in updateStore ol Null
        (_, Const p) -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to destruct '" ++ vn ++ "[" ++ show p ++ "]'. Variable is not an object array."
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to destruct '" ++ vn ++ "'. Variable is not an object array."

-- | Evaluation of copying a reference to a variable
evalCopyReference :: DataType -> (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalCopyReference IntegerType _ _ =      throwError "Copying is not supported for integers"
evalCopyReference (CopyType _) _ _ =     throwError "Copying is not supported for typed copy"
evalCopyReference ArrayType _ _ =        throwError "Copying is not supported for untyped array"
evalCopyReference ArrayElementType _ _ = throwError "Copying is not supported for array element"
evalCopyReference NilType _ _ =          throwError "Copying is not supported for nil"
evalCopyReference _ n m = addReference n m

-- | Evaluation of removing a reference to a variable
evalUnCopyReference :: DataType -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalUnCopyReference IntegerType _ =      throwError "Uncopying is not supported for integers"
evalUnCopyReference (CopyType _) _ =     throwError "Uncopying is not supported for typed copy"
evalUnCopyReference ArrayType _ =        throwError "Uncopying is not supported for untyped array"
evalUnCopyReference ArrayElementType _ = throwError "Uncopying is not supported for array element"
evalUnCopyReference NilType _ =          throwError "Uncopying is not supported for nil"
evalUnCopyReference _ (n, e) = do
    n' <- lookupVariableValue n
    evalUnCopyReference' n n' e
    where evalUnCopyReference' n (ObjectArray oa) (Just e) = do
            e' <- evalExpression e
            case e' of
                Const p -> do
                    checkOutOfBounds n oa p
                    sidx <- addToStore Null
                    let oa' = replaceNth p sidx oa
                     in updateBinding n $ ObjectArray oa'
                _ -> getIdentifierName n >>= \vn ->
                        throwError $ "No index was given to array '" ++ vn ++ "'"
          evalUnCopyReference' n (ObjectArray _) Nothing = addObjectBinding n Null
          evalUnCopyReference' n (Object _ _) Nothing = addObjectBinding n Null
          evalUnCopyReference' _ (IntegerArray _) _ = throwError "Uncopying is not supported for integer arrays"
          evalUnCopyReference' n _ Nothing = getIdentifierName n >>= \vn ->
            throwError $ "Unable to find valid object for uncopying in variable '" ++ vn ++ "'"
          evalUnCopyReference' n _ (Just e) = do
            vn <- getIdentifierName n
            e' <- evalExpression e
            case e' of
                Const p -> throwError $ "Unable to find valid object for uncopying in index '" ++ vn ++ "[" ++ show p ++ "]'"
                _ -> throwError $ "Unable to find valid object for uncopying in variable '" ++ vn ++ "'"

-- | Evaluation of constructing an int/object array
evalArrayConstruction :: SExpression -> SIdentifier -> Interpreter ()
evalArrayConstruction e n = do
    e' <- evalExpression e
    t <- getType n
    case (t, e') of
        (IntegerArrayType, Const len) ->
            let al = fromIntegral len
             in replicateM al (addToStore $ Const 0) >>= \cls ->
                    addObjectBinding n (IntegerArray cls)
        (ObjectArrayType _, Const len) ->
            let al = fromIntegral len
             in replicateM al (addToStore Null) >>= \ols ->
                    addObjectBinding n (ObjectArray ols)
        _ -> throwError $ "Unsupported array type " ++ show t

-- | Evaluation of destructing an int/object array
evalArrayDeconstruction :: SIdentifier -> Interpreter ()
evalArrayDeconstruction n = updateBinding n Null

-- | Evaluation of an scoped statement
evalStatement :: SStatement -> Interpreter ()
evalStatement (Assign n modop e) = evalAssign n modop e
evalStatement (AssignArrElem (n, e1) modop e2) = evalAssignArrElem (n, e1) modop e2
evalStatement (Swap t1 t2) = evalSwap t1 t2
evalStatement (Conditional e1 s1 s2 e2) = evalConditional e1 s1 s2 e2
evalStatement (Loop e1 s1 s2 e2) = evalLoop e1 s1 s2 e2
evalStatement (ObjectBlock tn n stmt) = evalObjectBlock tn n stmt
evalStatement (LocalBlock _ n e1 stmt e2) = evalLocalBlock n e1 stmt e2
evalStatement (LocalCall m args) = evalLocalCall m args
evalStatement (LocalUncall m args) = evalLocalUncall m args
evalStatement (ObjectCall o m args) = evalObjectCall o m args
evalStatement (ObjectUncall o m args) = evalObjectUncall o m args
evalStatement (ObjectConstruction tn (n, e)) = evalObjectConstruction tn (n, e)
evalStatement (ObjectDestruction _ (n, e)) = evalObjectDestruction (n, e)
evalStatement (CopyReference dt n m) = evalCopyReference dt n m
evalStatement (UnCopyReference dt _ m) = evalUnCopyReference dt m
evalStatement (ArrayConstruction (_, e) n) = evalArrayConstruction e n
evalStatement (ArrayDestruction _ n) = evalArrayDeconstruction n
evalStatement Skip = return ()

-- | Evaluation of the main method
evalMainMethod :: SIdentifier -> SProgram -> Interpreter ()
evalMainMethod mm1 ((_, GMDecl mm2 _ body) : rest)
    | mm1 == mm2 = mapM_ evalStatement body
    | otherwise = evalMainMethod mm1 rest
evalMainMethod _ [] = throwError "No main method found"

-- | Finds the type of a given scoped identifier
getType :: SIdentifier -> Interpreter DataType
getType n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable tp _) -> return tp
        Just (ClassField tp _ _ _) -> return tp
        Just (MethodParameter tp _) -> return tp
        Nothing -> getIdentifierName n >>= \vn -> throwError $ "No type matching " ++ vn

-- | Finds a classes', defined by its `TypeName`, fields/variables
getFields :: TypeName -> Interpreter [VariableDeclaration]
getFields tn = do
    cs <- gets (classes . caState . saState)
    case lookup tn cs of
        Just (GCDecl _ _ fs _) -> do
            scs <- getSuperClasses tn
            sfs <- findSuperClassFields scs
            return $ sfs ++ fs
        Nothing -> throwError $ "Unknown class '" ++ tn ++ "'"
    where findSuperClassFields [] = return []
          findSuperClassFields scs = concat <$> mapM getFields scs

-- | Retrieves the program from the state
getProgram :: Interpreter SProgram
getProgram = gets program

-- | Retrieves the main method scoped identifier
getMainMethod :: Interpreter SIdentifier
getMainMethod = gets (mainMethod . saState)

-- | Gets the typename of the the main class
getMainClassName :: Interpreter TypeName
getMainClassName = gets (mainClass . caState . saState) >>=
    \case
        Just tn -> return tn
        Nothing -> throwError "No main class has been defined"

-- | Finds superclasses of a given class
getSuperClasses :: TypeName -> Interpreter [TypeName]
getSuperClasses tn = gets (superClasses . caState . saState) >>= \scs ->
    case lookup tn scs of
        Just scs' -> do
            scss <- concat <$> mapM getSuperClasses scs'
            return $ scs' ++ scss
        Nothing -> return []

-- | Finds a method from the program
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

-- | Gets an object method that matches a class typename, where the class has contains a matching method name
getObjectMethod :: TypeName -> MethodName -> Interpreter (SIdentifier, [SVariableDeclaration], [SStatement])
getObjectMethod tn m = do
    prog <- gets program
    st <- gets (symbolTable . saState)
    scs <- getSuperClasses tn
    case findClassMethod prog st (tn : scs) m of
        Just mt -> return mt
        Nothing -> throwError $ "Class '" ++ tn ++ "' does not contain method '" ++ m ++ "'"
    where findClassMethod [] _ _ _ = Nothing
          findClassMethod ((cn, GMDecl i ps stmt):cs) st tns mn
            | cn `elem` tns =
                case lookup i st of
                    Just (Method _ imn) -> 
                        if imn == mn then
                            Just (i, ps, stmt)
                        else
                            findClassMethod cs st tns mn  
                    _ -> Nothing
            | otherwise = findClassMethod cs st tns mn
            
-- | Converts a scoped identifier to an identifier
getIdentifierName :: SIdentifier -> Interpreter Identifier
getIdentifierName n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable _ id)   -> return id
        Just (ClassField _ id _ _)  -> return id
        Just (MethodParameter _ id) -> return id
        Just (Method _ id) -> return id
        _ -> throwError $ "Identifier '" ++ show n ++ "' does not exist in symbol table"

-- | Used for evaluating environment map to values. Uses a visitation list to avoid infinite recursion.
showEnvironment :: [Env] -> Env -> Interpreter [String]
showEnvironment vst env =
    mapM
      ( \(k, l) ->
          getIdentifierName k
            >>= \k' ->
              lookupStore l
                >>= (showValueString vst 
                    >=> (\v' -> return $ show k' ++ ": " ++ v'))
      )
      (Map.toList env)

-- | Converts environment AST to more readable format by expanding data fields
showValueString :: [Env] -> IExpression -> Interpreter String
showValueString _ (Const v) = return $ show v
showValueString _ (IntegerArray ia) = do
    ia' <- mapM (lookupStore >=> showValueString []) ia
    return $ toArrayString ia'
showValueString vst (Object _ o) = 
    if o `elem` vst then
        return ""
    else 
        showEnvironment (o : vst) o >>= \o' ->
            let valueString = intercalate ", " o'
             in return $ toObjectString valueString
showValueString vst (ObjectArray oa) = 
    mapM (lookupStore >=> \l' -> showValueString vst l') oa 
        >>= \oa' -> return $ toArrayString oa'
showValueString _ Null = return "\"nil\""

-- | Initializes an class object
initializeObject :: TypeName -> [VariableDeclaration] -> Interpreter ()
initializeObject tn fs = do
    st <- gets (symbolTable . saState)
    scs <- getSuperClasses tn
    let ds = map (getFieldId st (tn : scs)) fs
     in mapM_ (uncurry addObjectBinding) ds
    where getFieldId [] tns (GDecl _ fn) = error $ "Field '" ++ fn ++ "' in class '" ++ show tns ++ "' does not exist in symbol table"
          getFieldId ((i, ClassField stp sfn stn _):st) tns f@(GDecl tp fn)
            | fn == sfn && tp == stp && stn `elem` tns = 
                let ne = case tp of
                            IntegerType -> Const 0
                            ObjectType _ -> Null
                            IntegerArrayType -> Null
                            ObjectArrayType _ -> Null
                            _ -> error $ "Unsupported datatype: '" ++ show tp ++ "'"
                 in (i, ne)
            | otherwise = getFieldId st tns f
          getFieldId (_:st) tns f = getFieldId st tns f

-- | Evaluation of a program's main method
evalProgram :: Interpreter String
evalProgram = do
    p <- getProgram
    mm <- getMainMethod
    mc <- getMainClassName
    fs <- getFields mc
    enterObjectScope Map.empty
    initializeObject mc fs
    evalMainMethod mm p
    env <- leaveObjectScope
    out <- showEnvironment [] env
    return $ toObjectString $ intercalate ", " out

toObjectString :: String -> String
toObjectString s = "{ " ++ s ++ " }"

toArrayString :: [String] -> String
toArrayString ss = "[" ++ intercalate ", " ss ++ "]"

-- | Interpretation using a scoped program and scoped analysis state
interpret :: (SProgram, SAState) -> Except String String
interpret (p, s) = fst <$> runStateT (runInt evalProgram) (initialState p s)
