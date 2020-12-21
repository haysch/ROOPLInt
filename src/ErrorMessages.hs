module ErrorMessages where

import Text.Printf
import AST
import Data.List
import Error
import Stringify

errorCause :: Cause -> RooplError
errorCause c = RooplError c []

emptyScopeStackException :: String -> RooplError 
emptyScopeStackException = errorCause . Trace . printf "Empty %s scope stack"

unknownLocationException :: Identifier -> RooplError
unknownLocationException "" = errorCause . Trace $ "Unable to find location"
unknownLocationException vn = errorCause . Trace $ printf "Unable to find location for '%s'" vn

outOfBoundsException :: Integer -> String -> RooplError
outOfBoundsException i arr = errorCause . Trace $ printf "Index %d was out of bounds for array '%s'" i arr

typeMatchException :: [String] -> DataType -> RooplError
typeMatchException expected dt =
    errorCause . Trace $ printf "Cannot match expected type '%s' with actual type '%s'" (intercalate ", " expected) (fromDataType dt)
    where fromDataType IntegerType = "int"
          fromDataType IntegerArrayType = "int[]"
          fromDataType (ObjectType tn) = tn
          fromDataType (ObjectArrayType tn) = printf "%s[]" tn
          fromDataType NilType = "nil"
          fromDataType dt = "unknown datatype: " ++ show dt

valueMatchException :: String -> String -> RooplError
valueMatchException expected actual = errorCause . Trace $ printf "Cannot match expected value '%s' with actual value '%s'" expected actual

divisionByZeroException :: RooplError
divisionByZeroException = errorCause $ Trace "Division by zero"

binaryOperationException :: BinOp -> IExpression -> IExpression -> RooplError
binaryOperationException binop ie1 ie2 =
    errorCause . Trace $ printf "Binary operation '%s %s %s' not legal" (stringifyIExpression ie1) (stringifyBinOp binop) (stringifyIExpression ie2)

modOperationException :: ModOp -> Identifier -> IExpression -> RooplError
modOperationException modop vn ie =
    errorCause . Trace $ printf "Mod operation '%s %s %s' not legal" vn vn (stringifyModOp modop) (stringifyIExpression ie)

undefinedVariableException :: Identifier -> RooplError
undefinedVariableException = errorCause . Trace . printf "Variable '%s' has not been defined"

callUninitializedObjectException :: RooplError
callUninitializedObjectException = errorCause $ Trace "Calling uninitialized object"

uncallUninitializedObjectException :: RooplError
uncallUninitializedObjectException = errorCause $ Trace "Uncalling uninitialized object"

copyException :: DataType -> RooplError
copyException dt = errorCause . Trace $ printf "Copying is not supported for %s. Expected object." (stringifyDataType dt)

uncopyException :: DataType -> RooplError
uncopyException dt = errorCause . Trace $ printf "Uncopying is not supported for %s. Expected object." (stringifyDataType dt)

conditionalAssertionException :: Bool -> RooplError
conditionalAssertionException b = errorCause . Trace $ printf "Exit assertion does not match entry. Should be %s" (fromBool b)
    where fromBool True = "true"
          fromBool False = "false"

mainMethodException :: RooplError
mainMethodException = errorCause $ Trace "No main method has been defined"

mainClassException :: RooplError
mainClassException = errorCause $ Trace "No main class has been defined"

undefinedMethodException :: RooplError
undefinedMethodException = errorCause $ Trace "Undefined method"

undefinedClassMethodException :: TypeName -> MethodName -> RooplError
undefinedClassMethodException tn mn = errorCause . Trace $ printf "Class '%s' does not contain method '%s'" tn mn

undefinedIdentifier :: RooplError
undefinedIdentifier = errorCause . Trace $ "Identifier does not exist in symbol table"

unknownException :: String -> RooplError
unknownException = errorCause . Trace

stringifyIExpression :: IExpression -> String
stringifyIExpression (Const _) = "int"
stringifyIExpression (IntegerArray _) = "int[]"
stringifyIExpression (Object tn _) = tn
stringifyIExpression (ObjectArray tn _) = printf "%s[]" tn
stringifyIExpression Null = "nil"