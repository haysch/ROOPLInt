module Stringify where

import AST
import Text.Printf (printf)
import Data.List (intercalate)

lookupId :: SIdentifier -> SymbolTable -> String
lookupId n st =
    case lookup n st of
        Just sym -> getIdFromSymbol sym
        Nothing -> error "No symbol matching the scoped identifier: " ++ show n
    where getIdFromSymbol (LocalVariable _ id) = id
          getIdFromSymbol (ClassField _ id _ _) = id
          getIdFromSymbol (MethodParameter _ id) = id
          getIdFromSymbol (Method _ id) = id

statementShorthand :: String
statementShorthand = "..."

stringifyDataType :: DataType -> String
stringifyDataType IntegerType = "int"
stringifyDataType (ObjectType tn) = tn
stringifyDataType (ObjectArrayType tn) = tn ++ "[]"
stringifyDataType IntegerArrayType = "int[]"
stringifyDataType NilType = "nil"
stringifyDataType dt = error $ "Unsupported datatype: " ++ show dt

stringifyBinOp :: BinOp -> String
stringifyBinOp Add    = "+"
stringifyBinOp Sub    = "-"
stringifyBinOp Xor    = "^"
stringifyBinOp Mul    = "*"
stringifyBinOp Div    = "/"
stringifyBinOp Mod    = "%"
stringifyBinOp BitAnd = "&"
stringifyBinOp BitOr  = "|"
stringifyBinOp And    = "&&"
stringifyBinOp Or     = "||"
stringifyBinOp Lt     = "<"
stringifyBinOp Gt     = ">"
stringifyBinOp Eq     = "="
stringifyBinOp Neq    = "!="
stringifyBinOp Lte    = "<="
stringifyBinOp Gte    = ">="

stringifyModOp :: ModOp -> String
stringifyModOp ModAdd = "+="
stringifyModOp ModSub = "-="
stringifyModOp ModXor = "^="

stringifySExpression :: SExpression -> SymbolTable -> String
stringifySExpression (Constant n) _ = show n
stringifySExpression (Variable v) st = lookupId v st
stringifySExpression (ArrayElement (n, e)) st =
    let n' = lookupId n st
        e' = stringifySExpression e st
     in printf "%s[%s]" n' e'
stringifySExpression Nil _ = "nil"
stringifySExpression (Binary binop e1 e2) st =
    let binop' = stringifyBinOp binop
        e1' = stringifySExpression e1 st
        e2' = stringifySExpression e2 st
     in unwords [e1', binop', e2']

stringifyVariable :: (SIdentifier, Maybe SExpression) -> SymbolTable -> String
stringifyVariable (n, Nothing) = lookupId n
stringifyVariable (n, Just e) = stringifySExpression $ ArrayElement (n, e)

stringifySStatement :: SStatement -> SymbolTable -> String
stringifySStatement (Assign n modop e) st =
    let n' = lookupId n st
        modop' = stringifyModOp modop
        e' = stringifySExpression e st
     in unwords [n', modop', e']
stringifySStatement (AssignArrElem e1 modop e2) st =
    let e1' = stringifySExpression (ArrayElement e1) st
        modop' = stringifyModOp modop
        e2' = stringifySExpression e2 st
     in unwords [e1', modop', e2']
stringifySStatement (Swap v1 v2) st =
    let v1' = stringifyVariable v1 st
        v2' = stringifyVariable v2 st
     in printf "%s <=> %s" v1' v2'
stringifySStatement (Conditional e1 _ _ e2) st =
    let e1' = stringifySExpression e1 st
        e2' = stringifySExpression e2 st
     in printf "if %s then ... else ... fi %s" e1' e2'
stringifySStatement (Loop e1 _ _ e2) st =
    let e1' = stringifySExpression e1 st
        e2' = stringifySExpression e2 st
     in printf "from %s do ... loop ... until %s" e1' e2'
stringifySStatement (ObjectBlock otn n _) st =
    let n' = lookupId n st
        con' = printf "construct %s %s" otn n'
        des' = printf "destruct %s" n'
     in unwords [con', statementShorthand, des']
stringifySStatement (LocalBlock dt n e1 _ e2) st =
    let dt' = stringifyDataType dt
        n' = lookupId n st
        e1' = printf "local %s %s = %s" dt' n' $ stringifySExpression e1 st
        e2' = printf "delocal %s %s = %s" dt' n' $ stringifySExpression e2 st
     in unwords [e1', statementShorthand, e2']
stringifySStatement (LocalCall m args) st =
    let args' = intercalate ", " $ map (`stringifyVariable` st) args
     in printf "call %s(%s)" m args'
stringifySStatement (LocalUncall m args) st =
    let args' = intercalate ", " $ map (`stringifyVariable` st) args
     in printf "uncall %s(%s)" m args'
stringifySStatement (ObjectCall o m args) st =
    let o' = stringifyVariable o st
        args' = intercalate ", " $ map (`stringifyVariable` st) args
     in printf "call %s::%s(%s)" o' m args'
stringifySStatement (ObjectUncall o m args) st =
    let o' = stringifyVariable o st
        args' = intercalate ", " $ map (`stringifyVariable` st) args
     in printf "uncall %s::%s(%s)" o' m args'
stringifySStatement (ObjectConstruction otn o) st =
    let o' = stringifyVariable o st
     in printf "new %s %s" otn o'
stringifySStatement (ObjectDestruction otn o) st =
    let o' = stringifyVariable o st
     in printf "delete %s %s" otn o'
stringifySStatement (CopyReference dt v1 v2) st =
    let dt' = stringifyDataType dt
        v1' = stringifyVariable v1 st
        v2' = stringifyVariable v2 st
     in printf "copy %s %s %s" dt' v1' v2'
stringifySStatement (UnCopyReference dt v1 v2) st =
    let dt' = stringifyDataType dt
        v1' = stringifyVariable v1 st
        v2' = stringifyVariable v2 st
     in printf "uncopy %s %s %s" dt' v1' v2'
stringifySStatement (ArrayConstruction (tn, e) n) st =
    let e' = stringifySExpression e st
        n' = lookupId n st
     in printf "new %s[%s] %s" tn e' n'
stringifySStatement (ArrayDestruction (tn, e) n) st =
    let e' = stringifySExpression e st
        n' = lookupId n st
     in printf "delete %s[%s] %s" tn e' n'
stringifySStatement Skip _ = "skip"

stringifyIExpression :: IExpression -> String
stringifyIExpression (Const _) = "int"
stringifyIExpression (IntegerArray _) = "int[]"
stringifyIExpression (Object tn _) = tn
stringifyIExpression (ObjectArray tn _) = printf "%s[]" tn
stringifyIExpression Null = "nil"
