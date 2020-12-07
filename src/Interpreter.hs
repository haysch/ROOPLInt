{-# LANGUAGE LambdaCase #-}
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
import Data.List

type IObject = Env
type ObjectScope = [IObject]

data IExpression = Const Integer
                 | Object IObject
                 | IntegerArray [Integer]
                 | ObjectArray [IExpression]
                 | Nil
    deriving (Show, Eq)

type Loc = SIdentifier
type Env = Map SIdentifier (Loc, Maybe SExpression)
type Store = Map Loc IExpression

data InterpreterState =
    InterpreterState {
        program :: SProgram,
        saState :: SAState,
        caller :: Env,
        objectScope :: ObjectScope,
        store :: Store,
        storeIndex :: SIdentifier
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
        store = Map.empty,
        storeIndex = 0
    }

-- | Replaces the n'th entry in a list
replaceNth :: Integer -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth p v (x:xs)
    | p == 0  = v:xs
    | otherwise = x:replaceNth (p - 1) v xs

-- | Returns the current object scope
topObjectScope :: Interpreter IObject
topObjectScope = gets objectScope >>= 
    \case
        (e:_) -> return e
        [] -> throwError "Empty object scope stack"

-- | Enters a new object scope using an object's environment as reference and sets caller to the calling object's environment, if any exists
enterObjectScope :: IObject -> Interpreter ()
enterObjectScope env = gets objectScope >>= \os ->
    let clr = case os of
                (o:_) -> o
                [] -> Map.empty
     in modify $ \s -> s { caller = clr, objectScope = env : objectScope s}

-- | Leaves the current object scope and returns its updated environment
leaveObjectScope :: Interpreter IObject
leaveObjectScope = do
    curr <- topObjectScope
    modify $ \s -> s { caller = Map.empty, objectScope = drop 1 (objectScope s) }
    return curr

-- | Adds variable binding to store and maps the reference to the current object environment
addObjectBinding :: SIdentifier -> IExpression -> Interpreter ()
addObjectBinding n e = do
    os <- topObjectScope
    store <- gets store
    storeIdx <- gets storeIndex
    let os' = Map.insert n (storeIdx, Nothing) os
        store' = Map.insert storeIdx e store
     in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s), store = store', storeIndex = 1 + storeIdx }

-- | Fetches the binding location of an identifier
getBindingLocation :: SIdentifier -> Interpreter (Loc, Maybe SExpression)
getBindingLocation n = topObjectScope >>= \os ->
    case Map.lookup n os of
        Just b -> return b
        Nothing -> getIdentifierName n >>= \vn ->
            throwError $ "Unknown reference of variable '" ++ vn ++ "'"

-- | Updates a binding in the store
updateBinding :: SIdentifier -> IExpression -> Interpreter ()
updateBinding n e = getBindingLocation n >>= \(loc, _) -> updateStore e loc
    where updateStore :: IExpression -> Loc -> Interpreter ()
          updateStore e loc = do
            store <- gets store
            let store' = Map.adjust (const e) loc store
             in modify $ \s -> s { store = store' }

-- | Adds a variable reference to the environment
addReference :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
addReference (n1, Nothing) (n2, Nothing) = do
    os <- topObjectScope
    case Map.lookup n1 os of
        Just l -> do
            let os' = Map.insert n2 l os
             in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s) }
        Nothing -> do
            cl <- gets caller
            case Map.lookup n1 cl of
                Just l -> 
                    let os' = Map.insert n2 l os
                     in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s) }
                Nothing -> 
                    getIdentifierName n1 >>= \vn ->
                        throwError $ "Unable to find location for '" ++ show (vn, n1) ++ "'"
addReference (n1, Just p) (n2, Nothing) = do
    cl <- gets caller
    case Map.lookup n1 cl of
        Just (l, _) -> do
            os <- topObjectScope
            let os' = Map.insert n2 (l, Just p) os
             in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s) }
        Nothing -> getIdentifierName n1 >>= \vn ->
            throwError $ "Unable to find location for '" ++ vn ++ "'"
-- addReference (n1, Just p1) (n2, Just p2) =

-- | Removes a variable reference from the environment
removeReference :: SIdentifier -> Interpreter ()
removeReference n = topObjectScope >>= \os ->
    let os' = Map.delete n os
     in modify $ \s -> s { objectScope = os' : drop 1 (objectScope s) }

-- | Looks up location in store to get the value
lookupStore :: SIdentifier -> Interpreter IExpression
lookupStore l = gets store >>= \store ->
    case Map.lookup l store of
        Just e -> return e
        Nothing -> throwError $ "Unknown location " ++ show l

-- | Looks up a reference in the environment to find value in store
lookupVariableValue :: SIdentifier -> Interpreter (IExpression, Maybe SExpression)
lookupVariableValue n = topObjectScope >>= \os ->
    case Map.lookup n os of
        Just (loc, offset) -> lookupStore loc >>= \loc' ->
            return (loc', offset)
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
        (Interpreter.Nil, Const _) -> return $ Const 0
        (Interpreter.Nil, Interpreter.Nil) -> return . Const $ evalOp binop 1 1
        (Object _, Interpreter.Nil) -> return . Const $ evalOp binop 1 0
        (Interpreter.Nil, Object _) -> return . Const $ evalOp binop 0 1
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
evalExpression (Variable v) = lookupVariableValue v >>= \(v', _) -> return v'
evalExpression (ArrayElement (v, e)) = do
    (v', _) <- lookupVariableValue v
    e' <- evalExpression e
    case (v', e') of
        (IntegerArray ia, Const p) ->
            checkOutOfBounds v ia p >>
                let v = ia !! fromIntegral p
                 in return $ Const v
        (ObjectArray oa, Const p) ->
            checkOutOfBounds v oa p >>
                case oa !! fromIntegral p of
                    Object o -> return $ Object o
                    exp -> throwError $ "Invalid entry in object array: '" ++ show exp ++ "'"
        _ -> getIdentifierName v >>= \vn ->
            throwError $ "Unable to find array '" ++ vn ++ "'"
evalExpression AST.Nil = return Interpreter.Nil
evalExpression (Binary binop e1 e2) = evalBinOp binop e1 e2

-- | Evaluates a variable assignment of a scoped expression
evalAssign :: SIdentifier -> ModOp -> SExpression -> Interpreter ()
evalAssign n modop e = do
    n' <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        ((Const v1, _), Const v2) ->
            let res = Const $ evalModOp modop v1 v2
             in updateBinding n res
        ((IntegerArray _, Just p), _) ->
            evalAssignArrElem (n, p) modop e
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Operation '" ++ show modop ++ "' not possible for '" ++ vn ++ "'"
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

-- | Evaluates an array index assignment of a scoped expression
evalAssignArrElem :: (SIdentifier, SExpression) -> ModOp -> SExpression -> Interpreter ()
evalAssignArrElem (n, e1) modop e2 = do
    (n', _) <- lookupVariableValue n
    e1' <- evalExpression e1
    e2' <- evalExpression e2
    case (n', e1', e2') of
        (IntegerArray ia, Const p, Const v2) ->
            checkOutOfBounds n ia p >>
                let v = ia !! fromIntegral p
                    res = evalModOp modop v v2
                    ia' = replaceNth p res ia
                 in updateBinding n $ IntegerArray ia'
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Operation '" ++ show modop ++ "' not possible for '" ++ vn ++ "'"
    where evalModOp ModAdd = (+)
          evalModOp ModSub = (-)
          evalModOp ModXor = xor

-- | Evaluates a swap between values in arrays and variables, and arrays to arrays
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
            oa1' = replaceNth p1 (Object o2) oa1
         in updateBinding n1 (ObjectArray oa1') >> 
                updateBinding n2 o1
swapArrayValues (n1, Object o1) Nothing (n2, ObjectArray oa2) (Just p2) =
    checkOutOfBounds n2 oa2 p2 >>
        let o2 = oa2 !! fromIntegral p2
            oa2' = replaceNth p2 (Object o1) oa2
         in updateBinding n1 o2 >> 
                updateBinding n2 (ObjectArray oa2')
swapArrayValues (n1, ObjectArray oa1) (Just p1) (n2, ObjectArray oa2) (Just p2) =
    checkOutOfBounds n1 oa1 p1 >> checkOutOfBounds n2 oa2 p2 >>
        let o1 = oa1 !! fromIntegral p1
            o2 = oa2 !! fromIntegral p2
            oa1' = replaceNth p1 o2 oa1
            oa2' = replaceNth p2 o1 oa2
         in updateBinding n1 (ObjectArray oa1') >> 
                updateBinding n2 (ObjectArray oa2')
swapArrayValues (n1, _) _ (n2, _) _ = do
    vn1 <- getIdentifierName n1
    vn2 <- getIdentifierName n2
    throwError $ "Unable to swap array values between '" ++ vn1 ++ "' and '" ++ vn2 ++ "'"

-- | Evaluates a swap between variables
evalSwap :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalSwap s1 s2 = if s1 == s2 then return () else performSwap s1 s2
    where performSwap (n1, m1) (n2, m2) =
            case (m1, m2) of
                (Just e1, Nothing) -> do
                    e1' <- evalExpression e1
                    (n1', _) <- lookupVariableValue n1
                    (n2', _) <- lookupVariableValue n2
                    case e1' of
                        Const p1 -> swapArrayValues (n1, n1') (Just p1) (n2, n2') Nothing
                        _ -> throwError "Unable to find position for swapping"
                (Nothing, Just e2) -> do
                    e2' <- evalExpression e2
                    (n1', _) <- lookupVariableValue n1
                    (n2', _) <- lookupVariableValue n2
                    case e2' of
                        Const p2 -> swapArrayValues (n1, n1') Nothing (n2, n2') (Just p2)
                        _ -> throwError "Unable to find position for swapping"
                (Just e1, Just e2) -> do
                    e1'  <- evalExpression e1
                    e2'  <- evalExpression e2
                    (n1', _) <- lookupVariableValue n1
                    (n2', _) <- lookupVariableValue n2
                    case (e1', e2') of
                        (Const p1, Const p2) -> swapArrayValues (n1, n1') (Just p1) (n2, n2') (Just p2)
                        _ -> throwError "Unable to find position for swapping"
                (Nothing, Nothing) -> 
                    do (v1, _) <- lookupVariableValue n1
                       (v2, _) <- lookupVariableValue n2
                       updateBinding n1 v2 >> updateBinding n2 v1

-- | Evaluates a conditional statement with entry and exit assertion
evalConditional :: SExpression -> [SStatement] -> [SStatement] -> SExpression -> Interpreter ()
evalConditional e1 s1 s2 e2 = do
    e1' <- evalExpression e1
    if e1' /= Const 0 -- e1' is True
        then mapM_ evalStatement s1
        else mapM_ evalStatement s2
    e2' <- evalExpression e2
    when (e1' /= e2') $ -- test and assert not equal
        throwError "Entry and exit assertion are not equal"

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
evalObjectBlock :: SIdentifier -> [SStatement] -> Interpreter ()
evalObjectBlock n stmt =
    evalObjectConstruction (n, Nothing) >>
        mapM_ evalStatement stmt >>
            evalObjectDestruction (n, Nothing) >>
                removeReference n

-- | Evaluates a local block with exit assertion
evalLocalBlock :: SIdentifier -> SExpression -> [SStatement] -> SExpression -> Interpreter ()
evalLocalBlock n e1 stmt e2 = do
    e1' <- evalExpression e1
    addObjectBinding n e1'
    mapM_ evalStatement stmt
    (e1', _) <- lookupVariableValue n
    e2' <- evalExpression e2
    if e1' == e2' then 
        removeReference n
    else 
        getIdentifierName n >>= \vn ->
            showValueString e1' >>= \v1 ->
                showValueString e2' >>= \v2 ->
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
    stmt' <- reverse <$> mapM invertStatement stmt
    evalCall args ps stmt'

-- | Evaluation of calling an object method
evalObjectCall :: (SIdentifier, Maybe SExpression) -> MethodName -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalObjectCall (n, Nothing) m args = lookupVariableValue n >>=
    \case
        (Object oenv, Nothing) -> do
            enterObjectScope oenv
            otn <- getObjectTypeName n
            (ps, stmt) <- getObjectMethod otn m
            evalCall args ps stmt
            oenv' <- leaveObjectScope
            updateBinding n $ Object oenv'
        (Interpreter.Nil, _) -> getIdentifierName n >>= \vn ->
            throwError $ "Calling object '" ++ vn ++ "' has not been initialized"
        _ -> getIdentifierName n >>= \vn ->
            throwError $ "Unable to call object '" ++ vn ++ "'"

evalObjectUncall :: (SIdentifier, Maybe SExpression) -> MethodName -> [(SIdentifier, Maybe SExpression)] -> Interpreter ()
evalObjectUncall (n, Nothing) m args = lookupVariableValue n >>=
    \case
        (Object oenv, Nothing) -> do
            enterObjectScope oenv
            otn <- getObjectTypeName n
            (ps, stmt) <- getObjectMethod otn m
            stmt' <- reverse <$> mapM invertStatement stmt
            evalCall args ps stmt'
            oenv' <- leaveObjectScope
            updateBinding n $ Object oenv'
        (Interpreter.Nil, _) -> topObjectScope >>= \os -> gets store >>= \stre ->
            getIdentifierName n >>= \vn ->
            trace (printAST os) $ trace (printAST stre) $ throwError $ "Uncalling object '" ++ show (vn, n) ++ "::" ++ m ++ "'. Object has not been initialized"
        _ -> getIdentifierName n >>= \vn ->
            throwError $ "Unable to uncall object '" ++ vn ++ "'"

-- | Evaluation of constructing an object
evalObjectConstruction :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectConstruction (n, Nothing) = do
    enterObjectScope Map.empty
    tn <- getObjectTypeName n
    fs <- getFields tn
    initializeObject tn fs
    o <- leaveObjectScope
    let obj = Object o
     in addObjectBinding n obj
evalObjectConstruction (n, Just e) = do
    (n', _) <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) ->
            checkOutOfBounds n oa p >>
                let o = Object Map.empty
                    oa' = replaceNth p o oa
                 in updateBinding n $ ObjectArray oa'

-- | Evaluation of destructing an object
evalObjectDestruction :: (SIdentifier, Maybe SExpression) -> Interpreter ()
evalObjectDestruction (n, Nothing) = updateBinding n Interpreter.Nil
evalObjectDestruction (n, Just e) = do
    (n', _) <- lookupVariableValue n
    e' <- evalExpression e
    case (n', e') of
        (ObjectArray oa, Const p) -> 
            checkOutOfBounds n oa p >>
                let oa' = replaceNth p Interpreter.Nil oa
                 in updateBinding n $ ObjectArray oa'
        _ -> getIdentifierName n >>= \vn ->
                throwError $ "Unable to destruction " ++ vn

-- | Evaluation of copying a reference to a variable
evalCopyReference :: (SIdentifier, Maybe SExpression) -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalCopyReference = addReference

-- | Evaluation of removing a reference to a variable
evalUnCopyReference :: DataType -> (SIdentifier, Maybe SExpression) -> Interpreter ()
evalUnCopyReference dt (n, _) =
    case dt of
        IntegerArrayType -> addObjectBinding n Interpreter.Nil
        (ObjectArrayType _) -> addObjectBinding n Interpreter.Nil
        _ -> throwError $ "Type '" ++ show dt ++ "' not supported for uncopying"

-- | Evaluation of constructing an int/object array
evalArrayConstruction :: SExpression -> SIdentifier -> Interpreter ()
evalArrayConstruction e n = do
    e' <- evalExpression e
    t <- getType n
    case (t, e') of
        (IntegerArrayType, Const l)  -> addObjectBinding n (IntegerArray $ replicate (fromIntegral l) 0)
        (ObjectArrayType _, Const l) -> addObjectBinding n (ObjectArray $ replicate (fromIntegral l) Interpreter.Nil)
        _ -> throwError $ "Unsupported array datatype " ++ show t

-- | Evaluation of destructing an int/object array
evalArrayDeconstruction :: SIdentifier -> Interpreter ()
evalArrayDeconstruction n = updateBinding n Interpreter.Nil

-- | Evaluation of an scoped statement
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
evalStatement (ObjectCall o m args) = evalObjectCall o m args
evalStatement (ObjectUncall o m args) = evalObjectUncall o m args
evalStatement (ObjectConstruction _ (n, e)) = evalObjectConstruction (n, e)
evalStatement (ObjectDestruction _ (n, e)) = evalObjectDestruction (n, e)
evalStatement (CopyReference _ n m) = evalCopyReference n m
evalStatement (UnCopyReference tp _ m) = evalUnCopyReference tp m
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

-- | Finds the object typename of a given scoped identifier
getObjectTypeName :: SIdentifier -> Interpreter TypeName
getObjectTypeName n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable (ObjectType tp) _) -> return tp
        Just (ClassField (ObjectType tp) _ _ _) -> return tp
        Just (MethodParameter (ObjectType tp) _) -> return tp
        Just (LocalVariable (ObjectArrayType tp) _) -> return tp
        Just (ClassField (ObjectArrayType tp) _ _ _) -> return tp
        Just (MethodParameter (ObjectArrayType tp) _) -> return tp
        Nothing -> getIdentifierName n >>= \vn ->
            throwError $ "Unable to determine object type for " ++ vn

-- | Finds a classes', defined by its `TypeName`, fields/variables
getFields :: TypeName -> Interpreter [VariableDeclaration]
getFields tn = do
    cs <- gets (classes . caState . saState)
    case lookup tn cs of
        Just (GCDecl _ _ fs _) -> return fs
        Nothing -> throwError $ "Unknown class '" ++ tn ++ "'"

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
getObjectMethod :: TypeName -> MethodName -> Interpreter ([SVariableDeclaration], [SStatement])
getObjectMethod tn m = do
    prog <- gets program
    st <- gets (symbolTable . saState)
    case findClassMethod prog st tn m of
        Just mt -> return mt
        Nothing -> throwError $ "No class matching '" ++ tn ++ "'"
    where findClassMethod [] _ _ _ = Nothing
          findClassMethod ((cn, GMDecl i ps stmt):cs) st tn mn
            | cn == tn =
                case lookup i st of
                    Just (Method _ imn) -> 
                        if imn == mn then
                            Just (ps, stmt)
                        else
                            findClassMethod cs st tn mn  
                    _ -> Nothing
            | otherwise = findClassMethod cs st tn mn
            
-- | Converts a scoped identifier to an identifier
getIdentifierName :: SIdentifier -> Interpreter Identifier
getIdentifierName n = gets (symbolTable . saState) >>= \st ->
    case lookup n st of
        Just (LocalVariable _ id)   -> return id
        Just (ClassField _ id _ _)  -> return id
        Just (MethodParameter _ id) -> return id
        _ -> throwError $ "Identifier '" ++ show n ++ "' does not exist in symbol table"

-- | Used for evaluating environment map to values
showEnvironment :: Env -> Interpreter [(Identifier, String)]
showEnvironment env =
    mapM
      ( \(k, (l, _)) ->
          getIdentifierName k
            >>= \k' ->
              lookupStore l
                >>= \v ->
                  showValueString v >>= \v' ->
                    return (k', v')
      )
      (Map.toList env)

-- TODO come up with a better way of constructing expression strings
showValueString :: IExpression -> Interpreter String
showValueString (Const v) = return $ show v
showValueString (Object o) = showEnvironment o >>= \o' ->
    let values = map (\(i, s) -> i ++ ": " ++ s) o'
        valueString = intercalate ", " values
     in return $ "Object { " ++ valueString ++ " }"
showValueString (ObjectArray oa) = mapM showValueString oa >>= \oa' ->
    return $ "[" ++ intercalate ", " oa' ++ "]"
showValueString Interpreter.Nil = return "Nil"

-- | Initializes an class object
initializeObject :: TypeName -> [VariableDeclaration] -> Interpreter ()
initializeObject tn fs = do
    st <- gets (symbolTable . saState)
    let ds = map (getFieldId st tn) fs
     in mapM_ (uncurry addObjectBinding) ds
    where getFieldId [] tn (GDecl _ fn) = error $ "Field '" ++ fn ++ "' in class '" ++ tn ++ "' does not exist in symbol table"
          getFieldId ((i, ClassField stp sfn stn _):st) tn f@(GDecl tp fn)
            | fn == sfn && tp == stp && tn == stn = 
                let ne = case tp of
                            IntegerType -> Const 0
                            ObjectType _ -> Interpreter.Nil
                            IntegerArrayType -> Interpreter.Nil
                            ObjectArrayType _ -> Interpreter.Nil
                            _ -> error $ "Unsupported datatype: '" ++ show tp ++ "'"
                 in (i, ne)
            | otherwise = getFieldId st tn f
          getFieldId (_:st) tn f = getFieldId st tn f

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
    -- TODO fix this mess - not very nice to read, only used for translating identifier integer to variable
    printAST <$> showEnvironment env

-- interpret :: (SProgram, SAState) -> Except String String
-- interpret (sprg, sastt) = return $ printAST sprg ++ printAST sastt

-- | Interpretation using a scoped program and scoped analysis state
interpret :: (SProgram, SAState) -> Except String String
interpret (p, s) = fst <$> runStateT (runInt evalProgram) (initialState p s) -- printAST . snd <$> -- for printing state
