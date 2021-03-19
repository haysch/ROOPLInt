module ErrorMessages where

import Text.Printf
import AST
import Data.List
import Error
import Stringify

-- | Wrapper for generating initial RooplError
errorCause :: Cause -> RooplError
errorCause c = RooplError c []

emptyScopeStackError :: String -> RooplError 
emptyScopeStackError = errorCause . Trace . printf "Empty %s scope stack"

unknownLocationError :: Identifier -> RooplError
unknownLocationError "" = errorCause . Trace $ "Unable to find location"
unknownLocationError vn = errorCause . Trace $ printf "Unable to find location for '%s'" vn

outOfBoundsError :: Integer -> String -> RooplError
outOfBoundsError i arr = errorCause . Trace $ printf "Index %d was out of bounds for array '%s'" i arr

typeMatchError :: [String] -> DataType -> RooplError
typeMatchError expected dt =
    errorCause . Trace $ printf "Cannot match expected type '%s' with actual type '%s'" (intercalate ", " expected) (fromDataType dt)
    where fromDataType IntegerType = "int"
          fromDataType IntegerArrayType = "int[]"
          fromDataType (ObjectType tn) = tn
          fromDataType (ObjectArrayType tn) = printf "%s[]" tn
          fromDataType NilType = "nil"
          fromDataType dt = "unknown datatype: " ++ show dt

valueMatchError :: String -> String -> RooplError
valueMatchError expected actual = errorCause . Trace $ printf "Cannot match expected value '%s' with actual value '%s'" expected actual

divisionByZeroError :: RooplError
divisionByZeroError = errorCause $ Trace "Division by zero"

binaryOperationError :: BinOp -> IExpression -> IExpression -> RooplError
binaryOperationError binop ie1 ie2 =
    errorCause . Trace $ printf "Binary operation '%s %s %s' not legal" (stringifyIExpression ie1) (stringifyBinOp binop) (stringifyIExpression ie2)

modOperationError :: ModOp -> Identifier -> IExpression -> RooplError
modOperationError modop vn ie =
    errorCause . Trace $ printf "Mod operation '%s %s %s' not legal" vn (stringifyModOp modop) (stringifyIExpression ie)

undefinedVariableError :: Identifier -> RooplError
undefinedVariableError = errorCause . Trace . printf "Variable '%s' has not been defined"

callUninitializedObjectError :: RooplError
callUninitializedObjectError = errorCause $ Trace "Calling uninitialized object"

uncallUninitializedObjectError :: RooplError
uncallUninitializedObjectError = errorCause $ Trace "Uncalling uninitialized object"

copyError :: DataType -> RooplError
copyError dt = errorCause . Trace $ printf "Copying is not supported for %s. Expected object." (stringifyDataType dt)

uncopyError :: DataType -> RooplError
uncopyError dt = errorCause . Trace $ printf "Uncopying is not supported for %s. Expected object." (stringifyDataType dt)

conditionalAssertionError :: Bool -> RooplError
conditionalAssertionError b = errorCause . Trace $ printf "Exit assertion does not match entry. Should be %s" (fromBool b)
    where fromBool True = "true"
          fromBool False = "false"

mainMethodError :: RooplError
mainMethodError = errorCause $ Trace "No main method has been defined"

mainClassError :: RooplError
mainClassError = errorCause $ Trace "No main class has been defined"

undefinedMethodError :: RooplError
undefinedMethodError = errorCause $ Trace "Undefined method"

undefinedClassMethodError :: TypeName -> MethodName -> RooplError
undefinedClassMethodError tn mn = errorCause . Trace $ printf "Class '%s' does not contain method '%s'" tn mn

undefinedIdentifier :: RooplError
undefinedIdentifier = errorCause . Trace $ "Identifier does not exist in symbol table"

unknownError :: String -> RooplError
unknownError = errorCause . Trace
