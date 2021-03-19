module Error where

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
data RooplError = RooplError Cause TraceStack

instance Show RooplError where
    show (RooplError c t) = 
        let cause = "Error thrown: " ++ show c
            traceStack = map show $ reverse t
         in printf "%s\n%s" cause (intercalate "\n\n" traceStack)

addTrace :: Trace -> RooplError -> RooplError
addTrace t (RooplError c s) = RooplError c $ t : s