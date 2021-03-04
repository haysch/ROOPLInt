{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Interpreter (interpret, Interpreter) where

import Control.Monad.Except

import qualified Data.Map as Map
import Data.Bits

import AST
import ScopeAnalyzer
import Control.Monad.State

import Debug.Trace (trace, traceShow)
import ClassAnalyzer
import Data.List
import Exception
import ExceptionMessages
import Stringify

data InterpreterState =
    InterpreterState {
        program :: SProgram,
        saState :: SAState,
        objectScope :: ObjectScope,
        referenceScope :: ReferenceScope,
        store :: Store,
        storeIndex :: SIdentifier,
        invCache :: [(SIdentifier, [SStatement])]
    } deriving (Show, Eq)

newtype Interpreter a = Interpreter { runInt :: StateT InterpreterState (Except RooplException) a }
    deriving (Functor, Applicative, Monad, MonadState InterpreterState, MonadError RooplException)

-- | Creating the initial interpreter state
initialState :: SProgram -> SAState -> InterpreterState
initialState p s = 
    InterpreterState {
        program = p,
        saState = s,
        objectScope = [],
        referenceScope = [],
        store = Map.empty,
        storeIndex = 0,
        invCache = []
    }

-- | Traces an expression execution and catches any errors to provide a trace
traceExpression :: SExpression -> Interpreter a -> Interpreter a
traceExpression e m = catchError m $ \err -> do
    st <- gets (symbolTable . saState)
    let e' = stringifySExpression e st
     in throwError $ addTrace (TraceExpression e') err

-- | Traces a statement execution and catches any errors to provide a trace
traceStatement :: SStatement -> Interpreter a -> Interpreter a
traceStatement stmt m = catchError m $ \err -> do
    tos <- topObjectScope
    ss <- serializeStore tos
    st <- gets (symbolTable . saState)
    let stmt' = stringifySStatement stmt st
     in throwError $ addTrace (TraceStatement stmt' ss) err

-- | Replaces the n'th entry in a list
replaceNth :: Integer -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth p v (x:xs)
    | p == 0  = v:xs
    | otherwise = x:replaceNth (p - 1) v xs

-- | Returns the caller of the current object, by returning the previous object
getCaller :: Interpreter Env
getCaller = gets objectScope >>=
    \case
        (_:c:_) -> return c -- more than one object in scope, return caller of current object
        [_] -> return Map.empty -- only one object in scope, main program object
        [] -> return Map.empty -- no object in scope, nothing to call from

-- | Returns the current object environment
topObjectScope :: Interpreter Env
topObjectScope = gets objectScope >>= 
    \case
        (e:_) -> return e
        [] -> throwError $ emptyScopeStackException "object"

-- | Returns the environment of the main class
mainObjectScope :: Interpreter Env
mainObjectScope = gets objectScope >>=
    \case
        os@(o:_) -> return $ last os
        [] -> throwError $ emptyScopeStackException "object"

-- | Returns the current reference scope
topReferenceScope :: Interpreter Ref
topReferenceScope = gets referenceScope >>=
    \case
        (r:_) -> return r
        [] -> throwError $ emptyScopeStackException "reference"

-- | Enters a new object scope using an object's environment as reference and sets caller to the calling object's environment, if any exists
enterObjectScope :: Env -> Interpreter ()
enterObjectScope env =
    modify $ \s -> s { objectScope = env : objectScope s, referenceScope = Map.empty : referenceScope s }

-- | Leaves the current object scope and returns its updated environment
leaveObjectScope :: Interpreter Env
leaveObjectScope = do
    curr <- topObjectScope
    modify $ \s -> s { objectScope = drop 1 (objectScope s), referenceScope = drop 1 (referenceScope s) }
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
            throwError $ undefinedVariableException vn

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
    cl <- getCaller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just l ->
            let os' = Map.insert n2 l os
                rs' = Map.insert n2 n1 rs
             in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ unknownLocationException vn
addReference (n1, Just p1) (n2, Nothing) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- getCaller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just l -> lookupStore l >>= \e1 ->
            evalExpression p1 >>= \p1' ->
            let os' = case (e1, p1') of
                        (IntegerArray ia, Const ip) ->
                            let il = ia !! fromIntegral ip
                             in Map.insert n2 il os
                        (ObjectArray _ oa, Const op) ->
                            let ol = oa !! fromIntegral op
                             in Map.insert n2 ol os
                rs' = Map.insert n2 n1 rs -- TODO: Add offset?
             in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ unknownLocationException vn
addReference (n1, Nothing) (n2, Just p2) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- getCaller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just l -> lookupVariableValue n2 >>= \e2 ->
            evalExpression p2 >>= \p2' ->
            case (e2, p2') of
                (IntegerArray ia, Const ip) ->
                    let ia' = replaceNth ip l ia
                     in updateBinding n2 $ IntegerArray ia'
                (ObjectArray tn oa, Const op) ->
                    let oa' = replaceNth op l oa
                     in updateBinding n2 $ ObjectArray tn oa'
            >> 
            let rs' = Map.insert n2 n1 rs -- TODO: Add offset?
             in modify $ \s -> s { referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ unknownLocationException vn
addReference (n1, Just p1) (n2, Just p2) = do
    os <- topObjectScope
    rs <- topReferenceScope
    cl <- getCaller
    let unionEnvs = Map.union os cl -- Unions current object and caller environment. Prefer current bindings
     in case Map.lookup n1 unionEnvs of
        Just _ -> do
            e1 <- lookupVariableValue n1
            e2 <- lookupVariableValue n2
            p1' <- evalExpression p1
            p2' <- evalExpression p2
            case (e1, p1', e2, p2') of
                (IntegerArray ia1, Const ip1, IntegerArray ia2, Const ip2) ->
                    let il1 = ia1 !! fromIntegral ip1
                        ia2' = replaceNth ip2 il1 ia2
                     in updateBinding n2 $ IntegerArray ia2'
                (ObjectArray _ oa1, Const op1, ObjectArray tn2 oa2, Const op2) ->
                    let ol1 = oa1 !! fromIntegral op1
                        oa2' = replaceNth op2 ol1 oa2
                     in updateBinding n2 $ ObjectArray tn2 oa2'
            >> 
            let rs' = Map.insert n2 n1 rs -- TODO: Add offset?
             in modify $ \s -> s { referenceScope = rs' : drop 1 (referenceScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
                    throwError $ unknownLocationException vn

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
        Nothing -> throwError $ unknownLocationException ""

-- | Looks up a reference in the environment to find value in store
lookupVariableValue :: SIdentifier -> Interpreter IExpression
lookupVariableValue n = topObjectScope >>= \os ->
    case Map.lookup n os of
        Just loc -> lookupStore loc >>= \e' ->
            return e'
        Nothing -> getCaller >>= \cl ->
            case Map.lookup n cl of
                Just loc -> lookupStore loc >>= \e' -> return e'
                Nothing -> getIdentifierName n >>= \vn -> 
                    throwError $ undefinedVariableException vn

-- | Checks whether an array index is out of bounds
checkOutOfBounds :: SIdentifier -> [a] -> Integer -> Interpreter ()
checkOutOfBounds n arr p =
    when (p < 0 || fromIntegral p > (length arr - 1)) $
        getIdentifierName n >>= \vn -> 
            throwError $ outOfBoundsException p vn

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

-- | Wrapper function for inverting statements by utilizing an inversion cache
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
        (Const v1, Const v2) -> 
            if v2 /= 0 
                then return . Const $ v1 `div` v2
                else throwError divisionByZeroException
        _ -> throwError $ binaryOperationException Div e1' e2'
evalBinOp binop e1 e2 = do
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (e1', e2') of
        (Const v1, Const v2) -> return . Const $ evalOp binop v1 v2
        (Null, Const _) -> return $ Const 0
        (Null, Null) -> return . Const $ evalOp binop 1 1
        (Object _ _, Null) -> return . Const $ evalOp binop 1 0
        (Null, Object _ _) -> return . Const $ evalOp binop 0 1
        _ -> throwError $ binaryOperationException binop e1' e2'
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
evalExpression sexp@(Constant n) = traceExpression sexp $ return $ Const n
evalExpression sexp@(Variable v) = traceExpression sexp $ lookupVariableValue v
evalExpression sexp@(ArrayElement (v, e)) =
    traceExpression sexp $ do
    v' <- lookupVariableValue v
    e' <- evalExpression e
    case (v', e') of
        (IntegerArray ia, Const p) ->
            checkOutOfBounds v ia p >>
                let vl = ia !! fromIntegral p
                 in lookupStore vl >>=
                     \case
                        Const v -> return $ Const v
                        ie -> showValueString [] ie >>= \ie' ->
                            throwError $ typeMatchException ["int"] (getExpressionDataType ie)
        (ObjectArray tn oa, Const p) ->
            checkOutOfBounds v oa p >>
                let ol = oa !! fromIntegral p
                 in lookupStore ol >>=
                    \case
                        Object tn o -> return $ Object tn o
                        ie -> showValueString [] ie >>= \ie' ->
                                throwError $ typeMatchException [tn] (getExpressionDataType ie)
        _ -> getIdentifierName v >>= \vn ->
            throwError $ undefinedVariableException vn
evalExpression Nil = traceExpression Nil $ return Null
evalExpression sexp@(Binary binop e1 e2) = traceExpression sexp $ evalBinOp binop e1 e2

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
                throwError $ modOperationException modop vn e'
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
                        ie -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
        (ie1, _, ie2) -> getIdentifierName n >>= \vn ->
            throwError $ modOperationException modop (stringifyIExpression ie1) ie2
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
                    ie -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
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
                    ie -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
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
                (Const _, ie2) -> throwError $ typeMatchException ["int"] (getExpressionDataType ie2)
                (ie1, Const _) -> throwError $ typeMatchException ["int"] (getExpressionDataType ie1)
                (_, _) -> throwError $ unknownException "Non-integer values in int[]"
swapArrayValues (n1, ObjectArray _ oa1) (Just p1) (n2, Object tn2 _) Nothing =
    checkOutOfBounds n1 oa1 p1 >> do
        l2 <- getBindingLocation n2
        let ol1 = oa1 !! fromIntegral p1
            oa1' = replaceNth p1 l2 oa1
         in lookupStore ol1 >>= 
             \case 
                (Object tn1 _) -> assertObjectTypes (tn1, n1) (tn2, n2) >>
                    updateBinding n1 (ObjectArray tn1 oa1') >> updateLocation n2 ol1
                ie -> throwError $ typeMatchException [tn2] (getExpressionDataType ie)
swapArrayValues (n1, Object tn1 _) Nothing (n2, ObjectArray _ oa2) (Just p2) =
    checkOutOfBounds n1 oa2 p2 >> do
        l1 <- getBindingLocation n1
        let ol2 = oa2 !! fromIntegral p2
            oa2' = replaceNth p2 l1 oa2
         in lookupStore ol2 >>= 
             \case 
                (Object tn2 _) -> assertObjectTypes (tn1, n1) (tn2, n2) >>
                    updateLocation n1 ol2 >> updateBinding n2 (ObjectArray tn2 oa2')
                ie -> throwError $ typeMatchException [tn1] (getExpressionDataType ie)
swapArrayValues (n1, ObjectArray _ oa1) (Just p1) (n2, ObjectArray _ oa2) (Just p2) =
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
                    updateBinding n1 (ObjectArray tn1 oa1') >> updateBinding n2 (ObjectArray tn2 oa2')
                (_, _) -> throwError $ unknownException "Objects do not match"
swapArrayValues (n1, _) _ (n2, _) _ = do
    vn1 <- getIdentifierName n1
    vn2 <- getIdentifierName n2
    throwError $ unknownException "Unable to swap"

-- | Asserts that the types used for swapping are equal
assertObjectTypes :: (TypeName, SIdentifier) -> (TypeName, SIdentifier) -> Interpreter ()
assertObjectTypes (tn1, n1) (tn2, n2) =
    when (tn1 /= tn2) $ do 
        vn1 <- getIdentifierName n1
        vn2 <- getIdentifierName n2
        throwError $ typeMatchException [tn1] (ObjectType tn2)

-- | Evaluates a swap between variables
evalSwap :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalSwap s1 s2 = if s1 == s2 then return () else performSwap s1 s2
    where performSwap (n1, Just e1) (n2, Nothing) = do
            e1' <- evalExpression e1
            n1' <- lookupVariableValue n1
            n2' <- lookupVariableValue n2
            case e1' of
                Const p1 -> swapArrayValues (n1, n1') (Just p1) (n2, n2') Nothing
                ie -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
          performSwap (n1, Nothing) (n2, Just e2) = do
            e2' <- evalExpression e2
            n1' <- lookupVariableValue n1
            n2' <- lookupVariableValue n2
            case e2' of
                Const p2 -> swapArrayValues (n1, n1') Nothing (n2, n2') (Just p2)
                ie -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
          performSwap (n1, Just e1) (n2, Just e2) = do
            e1'  <- evalExpression e1
            e2'  <- evalExpression e2
            n1' <- lookupVariableValue n1
            n2' <- lookupVariableValue n2
            case (e1', e2') of
                (Const p1, Const p2) -> swapArrayValues (n1, n1') (Just p1) (n2, n2') (Just p2)
                (ie, Const _) -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
                (Const _, ie) -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
                _ -> throwError $ unknownException "Unable to find array indices"
          performSwap (n1, Nothing) (n2, Nothing) = do
            l1 <- getBindingLocation n1
            l2 <- getBindingLocation n2
            updateLocation n1 l2 >> updateLocation n2 l1

-- | Updates every reference to a store location in the object scope. Used for updating location in current object or arguments, if any.
updateLocation :: SIdentifier -> Location -> Interpreter ()
updateLocation n l = do
    os <- gets objectScope
    rs <- gets referenceScope
    let os' = updateObjectScopeLoc n l os rs
     in modify $ \s -> s { objectScope = os' }

    where updateObjectScopeLoc :: SIdentifier -> Location -> ObjectScope -> ReferenceScope -> ObjectScope
          updateObjectScopeLoc _ _ [] [] = []
          updateObjectScopeLoc n l (o:ostack) (r:rstack) = 
              let o' = Map.adjust (const l) n o
               in case Map.lookup n r of
                    Just n' -> o' : updateObjectScopeLoc n' l ostack rstack
                    Nothing -> o' : ostack

-- | Evaluates a conditional statement with entry and exit assertion
evalConditional :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalConditional e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    if e1' /= Const 0 -- e1' is True
        then mapM_ evalStatement s1
        else mapM_ evalStatement s2
    e2' <- evalExpression e2
    when (e1' /= e2') $ -- test and assert not equal
        throwError $ conditionalAssertionException (truthy e1')
    where truthy (Const 0) = False
          truthy Null = False
          truthy _ = True

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
    else showValueString [] e1' >>= \actual ->
            showValueString [] e2' >>= \expected ->
                throwError $ valueMatchException expected actual

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
        Null -> throwError callUninitializedObjectException 
        ie -> throwError $ typeMatchException ["object"] (getExpressionDataType ie)
evalObjectCall (n, Just e) m args = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray _ oa, Const p) -> 
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
                        Null -> throwError callUninitializedObjectException
                        ie -> throwError $ typeMatchException ["object"] (getExpressionDataType ie)
        (ie, _) -> throwError $ typeMatchException ["object[]"] (getExpressionDataType ie)

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
                throwError uncallUninitializedObjectException
        ie -> throwError $ typeMatchException ["object"] (getExpressionDataType ie)
evalObjectUncall (n, Just e) m args = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray _ oa, Const p) -> 
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
                        Null -> throwError callUninitializedObjectException
                        ie -> throwError $ typeMatchException ["object"] (getExpressionDataType ie)
        (ie, _) -> throwError $ typeMatchException ["object[]"] (getExpressionDataType ie)

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
        (ObjectArray _ oa, Const p) ->
            checkOutOfBounds n oa p >>
                createObject tn >>= \o -> 
                    let ol = oa !! fromIntegral p
                     in updateStore ol (Object tn o)
        (ie, _) -> throwError $ typeMatchException ["object[]"] (getExpressionDataType ie)

-- | Evaluation of destructing an object
evalObjectDestruction :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectDestruction (n, Nothing) = addObjectBinding n Null
evalObjectDestruction (n, Just e) = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray _ oa, Const p) -> 
            checkOutOfBounds n oa p >>
                let ol = oa !! fromIntegral p
                 in updateStore ol Null
        (ie, _) -> throwError $ typeMatchException ["object[]"] (getExpressionDataType ie)

-- | Evaluation of copying a reference to a variable
evalCopyReference :: DataType -> (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalCopyReference IntegerType _ _ =      throwError $ copyException IntegerType
evalCopyReference dt@(CopyType _) _ _ =  throwError $ copyException dt
evalCopyReference ArrayType _ _ =        throwError $ copyException ArrayType
evalCopyReference ArrayElementType _ _ = throwError $ copyException ArrayElementType
evalCopyReference NilType _ _ =          throwError $ copyException NilType
evalCopyReference _ n m = addReference n m

-- | Evaluation of removing a reference to a variable
evalUnCopyReference :: DataType -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalUnCopyReference IntegerType _ =      throwError $ uncopyException IntegerType
evalUnCopyReference dt@(CopyType _) _ =  throwError $ uncopyException dt
evalUnCopyReference ArrayType _ =        throwError $ uncopyException ArrayType
evalUnCopyReference ArrayElementType _ = throwError $ uncopyException ArrayElementType
evalUnCopyReference NilType _ =          throwError $ uncopyException NilType
evalUnCopyReference _ (n, e) = do
    n' <- lookupVariableValue n
    evalUnCopyReference' n n' e
    where evalUnCopyReference' n (ObjectArray tn oa) (Just e) = do
            e' <- evalExpression e
            case e' of
                Const p -> do
                    checkOutOfBounds n oa p
                    sidx <- addToStore Null
                    let oa' = replaceNth p sidx oa
                     in updateBinding n $ ObjectArray tn oa'
                ie -> throwError $ typeMatchException ["int"] (getExpressionDataType ie)
          evalUnCopyReference' n (ObjectArray _ _) Nothing = addObjectBinding n Null
          evalUnCopyReference' n (Object _ _) Nothing = addObjectBinding n Null
          evalUnCopyReference' n ie _ = throwError $ typeMatchException ["object","object[]"] (getExpressionDataType ie)
          
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
        (ObjectArrayType tn, Const len) ->
            let al = fromIntegral len
             in replicateM al (addToStore Null) >>= \ols ->
                    addObjectBinding n (ObjectArray tn ols)
        (dt, _) -> throwError $ typeMatchException ["int[]", "object[]"] dt

-- | Evaluation of destructing an int/object array
evalArrayDeconstruction :: SIdentifier -> Interpreter ()
evalArrayDeconstruction n = updateBinding n Null

-- | Evaluation of an scoped statement
evalStatement :: SStatement -> Interpreter ()
evalStatement sstmt@(Assign n modop e)              = traceStatement sstmt $ evalAssign n modop e
evalStatement sstmt@(AssignArrElem (n, e1) modop e2)= traceStatement sstmt $ evalAssignArrElem (n, e1) modop e2
evalStatement sstmt@(Swap t1 t2)                    = traceStatement sstmt $ evalSwap t1 t2
evalStatement sstmt@(Conditional e1 s1 s2 e2)       = traceStatement sstmt $ evalConditional e1 s1 s2 e2
evalStatement sstmt@(Loop e1 s1 s2 e2)              = traceStatement sstmt $ evalLoop e1 s1 s2 e2
evalStatement sstmt@(ObjectBlock tn n stmt)         = traceStatement sstmt $ evalObjectBlock tn n stmt
evalStatement sstmt@(LocalBlock _ n e1 stmt e2)     = traceStatement sstmt $ evalLocalBlock n e1 stmt e2
evalStatement sstmt@(LocalCall m args)              = traceStatement sstmt $ evalLocalCall m args
evalStatement sstmt@(LocalUncall m args)            = traceStatement sstmt $ evalLocalUncall m args
evalStatement sstmt@(ObjectCall o m args)           = traceStatement sstmt $ evalObjectCall o m args
evalStatement sstmt@(ObjectUncall o m args)         = traceStatement sstmt $ evalObjectUncall o m args
evalStatement sstmt@(ObjectConstruction tn (n, e))  = traceStatement sstmt $ evalObjectConstruction tn (n, e)
evalStatement sstmt@(ObjectDestruction _ (n, e))    = traceStatement sstmt $ evalObjectDestruction (n, e)
evalStatement sstmt@(CopyReference dt n m)          = traceStatement sstmt $ evalCopyReference dt n m
evalStatement sstmt@(UnCopyReference dt _ m)        = traceStatement sstmt $ evalUnCopyReference dt m
evalStatement sstmt@(ArrayConstruction (_, e) n)    = traceStatement sstmt $ evalArrayConstruction e n
evalStatement sstmt@(ArrayDestruction _ n)          = traceStatement sstmt $ evalArrayDeconstruction n
evalStatement Skip                                  = traceStatement Skip  $ return ()

-- | Evaluation of the main method
evalMainMethod :: SIdentifier -> SProgram -> Interpreter ()
evalMainMethod mm1 ((_, GMDecl mm2 _ body) : rest)
    | mm1 == mm2 = mapM_ evalStatement body
    | otherwise = evalMainMethod mm1 rest
evalMainMethod _ [] = throwError mainMethodException

-- | Finds the type of a given scoped identifier
getType :: SIdentifier -> Interpreter DataType
getType n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable tp _) -> return tp
        Just (ClassField tp _ _ _) -> return tp
        Just (MethodParameter tp _) -> return tp
        Nothing -> getIdentifierName n >>= \vn -> throwError $ unknownException $ "No type matching: " ++ vn

-- | Finds the appropriate datatype for an interpreter expression
getExpressionDataType :: IExpression -> DataType
getExpressionDataType (Const _) = IntegerType
getExpressionDataType (IntegerArray _) = IntegerArrayType
getExpressionDataType (Object tn _) = ObjectType tn
getExpressionDataType (ObjectArray tn _) = ObjectArrayType tn
getExpressionDataType Null = NilType

-- | Finds a classes', defined by its `TypeName`, fields/variables
getFields :: TypeName -> Interpreter [VariableDeclaration]
getFields tn = do
    cs <- gets (classes . caState . saState)
    case lookup tn cs of
        Just (GCDecl _ _ fs _) -> do
            scs <- getSuperClasses tn
            sfs <- findSuperClassFields scs
            return $ sfs ++ fs
        Nothing -> throwError $ unknownException $ "Unknown class: " ++ tn
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
        Nothing -> throwError mainClassException

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
        Nothing -> throwError undefinedMethodException
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
        Nothing -> throwError $ undefinedClassMethodException tn m
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
        _ -> throwError undefinedIdentifier

-- | Used for evaluating environment map to values. Uses a visitation list to avoid infinite recursion.
showEnvironmentStore :: [Env] -> Env -> Interpreter [String]
showEnvironmentStore vst env =
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
        showEnvironmentStore (o : vst) o >>= \o' ->
            let valueString = intercalate ", " o'
             in return $ toObjectString valueString
showValueString vst (ObjectArray _ oa) = 
    mapM (lookupStore >=> \l' -> showValueString vst l') oa 
        >>= \oa' -> return $ toArrayString oa'
showValueString _ Null = return "nil"

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

-- | Serializes an environment to JSON-like syntax
serializeStore :: Env -> Interpreter String
serializeStore env = do
    store <- showEnvironmentStore [] env
    return $ toObjectString $ intercalate ", " store

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
    serializeStore env

-- | Wraps a string in curly brackets
toObjectString :: String -> String
toObjectString s = "{ " ++ s ++ " }"

-- | Converts a [String] to String by concatenating with ", " and wrapping in square brackets
toArrayString :: [String] -> String
toArrayString ss = "[" ++ intercalate ", " ss ++ "]"

-- | Interpretation using a scoped program and scoped analysis state
interpret :: (SProgram, SAState) -> Except String String
interpret (p, s) = 
    case runExcept $ runStateT (runInt evalProgram) (initialState p s) of
        Left err -> throwError $ show err
        Right res -> return $ fst res
