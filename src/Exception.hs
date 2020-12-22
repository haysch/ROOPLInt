module Exception where

import Data.List (intercalate)
import Text.Printf (printf)

data Trace = Trace String
           | TraceExpression String
           | TraceStatement String String

instance Show Trace where
    show (Trace s) = s
    show (TraceExpression s) = s
    show (TraceStatement stmt store) = 
        printf "    In \"%s\"\n    where %s\n" stmt store

type Cause = Trace
type TraceStack = [Trace]
data RooplException = RooplException Cause TraceStack

instance Show RooplException where
    show (RooplException c t) = 
        let cause = "Exception thrown: " ++ show c
            traceStack = map show $ reverse t
         in intercalate "\n" $ cause : traceStack

addTrace :: Trace -> RooplException -> RooplException
addTrace t (RooplException c s) = RooplException c $ t : s