import Control.Monad.Except
import System.IO
import System.Environment

import PISA
import Parser
import ClassAnalyzer
import ScopeAnalyzer
import TypeChecker
import CodeGenerator
import MacroExpander
import Interpreter

import Data.List.Split

type Error = String

main :: IO ()
main = 
    do  args <- getArgs
        when (null args) (error "Supply input filename.\nUsage: ROOPLInt [interpret|compile] input.rplpp [output.pal]\n")
        when (length args > 2) (error "Too many arguments.\nUsage: ROOPLInt input.rplpp\n")
        handle <- openFile (head args) ReadMode
        input <- hGetContents handle
        either (hPutStrLn stderr) (hPutStrLn stdout) $ interpretProgram input

interpretProgram :: String -> Either String String
interpretProgram s =
    runExcept $
    parseString s
    >>= classAnalysis
    >>= scopeAnalysis
    >>= typeCheck
    >>= interpret

compileProgram :: String -> Either Error PISA.Program
compileProgram s =
    runExcept $
    parseString s
    >>= classAnalysis
    >>= scopeAnalysis
    >>= typeCheck
    >>= generatePISA
    >>= expandMacros
