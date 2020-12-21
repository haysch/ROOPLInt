module Error where

import AST
import Data.List (intercalate)
import Text.Printf

data Trace = Trace String
           | TraceStatement String String

instance Show Trace where
    show (Trace s) = s
    show (TraceStatement stmt store) = 
        printf "    In \"%s\"\n    where %s\n" stmt store

type Cause = Trace
type TraceStack = [Trace]
data RooplError = RooplError Cause TraceStack

instance Show RooplError where
    show (RooplError c t) = 
        let cause = "Exception thrown: " ++ show c
            traceStack = map show $ reverse t
         in intercalate "\n" $ cause : traceStack

addTrace :: Trace -> RooplError -> RooplError
addTrace t (RooplError c s) = RooplError c $ t : s