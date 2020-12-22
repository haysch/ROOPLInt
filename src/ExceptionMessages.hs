module ExceptionMessages where

import Text.Printf
import AST
import Data.List
import Exception
import Stringify

-- | Wrapper for generating initial RooplException
errorCause :: Cause -> RooplException
errorCause c = RooplException c []

emptyScopeStackException :: String -> RooplException 
emptyScopeStackException = errorCause . Trace . printf "Empty %s scope stack"

unknownLocationException :: Identifier -> RooplException
unknownLocationException "" = errorCause . Trace $ "Unable to find location"
unknownLocationException vn = errorCause . Trace $ printf "Unable to find location for '%s'" vn

outOfBoundsException :: Integer -> String -> RooplException
outOfBoundsException i arr = errorCause . Trace $ printf "Index %d was out of bounds for array '%s'" i arr

typeMatchException :: [String] -> DataType -> RooplException
typeMatchException expected dt =
    errorCause . Trace $ printf "Cannot match expected type '%s' with actual type '%s'" (intercalate ", " expected) (fromDataType dt)
    where fromDataType IntegerType = "int"
          fromDataType IntegerArrayType = "int[]"
          fromDataType (ObjectType tn) = tn
          fromDataType (ObjectArrayType tn) = printf "%s[]" tn
          fromDataType NilType = "nil"
          fromDataType dt = "unknown datatype: " ++ show dt

valueMatchException :: String -> String -> RooplException
valueMatchException expected actual = errorCause . Trace $ printf "Cannot match expected value '%s' with actual value '%s'" expected actual

divisionByZeroException :: RooplException
divisionByZeroException = errorCause $ Trace "Division by zero"

binaryOperationException :: BinOp -> IExpression -> IExpression -> RooplException
binaryOperationException binop ie1 ie2 =
    errorCause . Trace $ printf "Binary operation '%s %s %s' not legal" (stringifyIExpression ie1) (stringifyBinOp binop) (stringifyIExpression ie2)

modOperationException :: ModOp -> Identifier -> IExpression -> RooplException
modOperationException modop vn ie =
    errorCause . Trace $ printf "Mod operation '%s %s %s' not legal" vn vn (stringifyModOp modop) (stringifyIExpression ie)

undefinedVariableException :: Identifier -> RooplException
undefinedVariableException = errorCause . Trace . printf "Variable '%s' has not been defined"

callUninitializedObjectException :: RooplException
callUninitializedObjectException = errorCause $ Trace "Calling uninitialized object"

uncallUninitializedObjectException :: RooplException
uncallUninitializedObjectException = errorCause $ Trace "Uncalling uninitialized object"

copyException :: DataType -> RooplException
copyException dt = errorCause . Trace $ printf "Copying is not supported for %s. Expected object." (stringifyDataType dt)

uncopyException :: DataType -> RooplException
uncopyException dt = errorCause . Trace $ printf "Uncopying is not supported for %s. Expected object." (stringifyDataType dt)

conditionalAssertionException :: Bool -> RooplException
conditionalAssertionException b = errorCause . Trace $ printf "Exit assertion does not match entry. Should be %s" (fromBool b)
    where fromBool True = "true"
          fromBool False = "false"

mainMethodException :: RooplException
mainMethodException = errorCause $ Trace "No main method has been defined"

mainClassException :: RooplException
mainClassException = errorCause $ Trace "No main class has been defined"

undefinedMethodException :: RooplException
undefinedMethodException = errorCause $ Trace "Undefined method"

undefinedClassMethodException :: TypeName -> MethodName -> RooplException
undefinedClassMethodException tn mn = errorCause . Trace $ printf "Class '%s' does not contain method '%s'" tn mn

undefinedIdentifier :: RooplException
undefinedIdentifier = errorCause . Trace $ "Identifier does not exist in symbol table"

unknownException :: String -> RooplException
unknownException = errorCause . Trace
