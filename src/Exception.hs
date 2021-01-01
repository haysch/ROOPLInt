module Exception where

import Data.List (intercalate)
import Text.Printf (printf)

-- Based on an idea from Jana https://github.com/mbudde/jana

data Trace = Trace String
           | TraceExpression String
           | TraceStatement String String

instance Show Trace where
    show (Trace t) = t
    show (TraceExpression e) = 
        printf "  In \"%s\"" e
    show (TraceStatement stmt store) = 
        printf "  In \"%s\"\n  where %s" stmt store

type Cause = Trace
type TraceStack = [Trace]
data RooplException = RooplException Cause TraceStack

instance Show RooplException where
    show (RooplException c t) = 
        let cause = "Exception thrown: " ++ show c
            traceStack = map show $ reverse t
         in printf "%s\n%s" cause (intercalate "\n\n" traceStack)

addTrace :: Trace -> RooplException -> RooplException
addTrace t (RooplException c s) = RooplException c $ t : s