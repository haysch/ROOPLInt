import Control.Monad.Except
import System.IO
import System.Environment
import System.Timeout
import System.Exit

import AST
import PISA
import Parser
import ClassAnalyzer
import ScopeAnalyzer
import TypeChecker
import CodeGenerator
import MacroExpander
import Interpreter
import ProgramInverter

import Data.List
import Data.List.Split
import Debug.Trace (trace, traceShow)

type Error = String

data RunOpt = Compile
          | Interpret
          | Invert

data Options =
    Options {
        runOpt :: RunOpt,
        timeOut :: Int,
        output :: String
    }

defaultOpts :: Options
defaultOpts =
    Options {
        runOpt = Interpret,
        timeOut = -1,
        output = ""
    }

usage :: String
usage = "usage: ROOPLInt [-i|-c] input.rplpp [output.pal]\n\
        \options:\n\
        \ -i:           invert program\n\
        \ -c:           compile program\n\
        \ -o<FILENAME>: output compiled program (only when -c or -i is used)\n\
        \ -tN:          timeout after N seconds"

parseArgs :: IO (Maybe (String, Options))
parseArgs = do
    args <- getArgs
    when (null args) (error $ "Supply input filename.\n" ++ usage)
    let (flgs, fname) = partition (\a -> head a == '-' && length a > 1) args
     in do
         assertInputMethod fname
         case checkFlags flgs of
            Left err -> putStrLn err >> return Nothing
            Right opts -> return $ Just (head fname, opts)

assertInputMethod :: [String] -> IO ()
assertInputMethod fname = do
    when (null fname) (error $ "No file or input method specified. Specify one file or '-' to use stdin\n" ++ usage)
    when (length fname > 1) (error $ "More than one input method specified. Specify one file or '-' to use stdin\n" ++ usage)

checkFlags :: [String] -> Either Error Options
checkFlags = foldM setOption defaultOpts

setOption :: Options -> String -> Either Error Options
setOption opts "-i" = return $ opts { runOpt = Invert }
setOption opts "-c" = return $ opts { runOpt = Compile }
setOption opts ('-':'o':filename) = return $ opts { output = filename }
setOption opts ('-':'t':time) =
    case reads time of
        [(val,"")] -> return $ opts { timeOut = val * 1000000 } -- convert to seconds
        _          -> Left "Non-integer provided in the -t option"
setOption _ f = Left $ "invalid option: " ++ f

getFileContent :: String -> IO String            
getFileContent "-" = getContents
getFileContent fname = do
    handle <- openFile fname ReadMode
    hGetContents handle

writeOut :: String -> String -> String -> IO ()
writeOut "-" "" content = putStrLn content
writeOut defaultName "" content =
    let fname = head (splitOn "." defaultName) ++ "-inverted.rplpp"
     in writeFile fname content
writeOut _ outfile content = writeFile outfile content

parseAndAnalysis :: String -> Except Error (SProgram, SAState)
parseAndAnalysis s =
    parseString s
    >>= classAnalysis
    >>= scopeAnalysis
    >>= typeCheck

interpretProgram :: String -> Either Error String
interpretProgram s =
    runExcept $
    parseAndAnalysis s
    >>= interpret

invertProgram :: String -> Either Error String
invertProgram s =
    runExcept $
    parseAndAnalysis s
    >>= invert

compileProgram :: String -> Either Error PISA.Program
compileProgram s =
    runExcept $
    parseAndAnalysis s
    >>= generatePISA
    >>= expandMacros

main :: IO ()
main = 
    do  args <- parseArgs
        case args of
            -- Interpretation
            Just (file, opts@Options { runOpt = Interpret }) ->
                getFileContent file >>= \input -> do
                    res <- timeout (timeOut opts) (return $ interpretProgram input)
                    case res of
                        Nothing -> exitWith $ ExitFailure 100
                        Just res' -> either (hPutStrLn stderr) putStrLn res'
            -- Invert
            Just (file, Options { runOpt = Invert, output = outfile }) ->
                getFileContent file >>= \input ->
                    either (hPutStrLn stderr) (writeOut file outfile) $ invertProgram input
            -- Compile
            Just (file, Options { runOpt = Compile, output = outfile }) ->
                getFileContent file >>= \input ->
                    either (hPutStrLn stderr) (writeOut file outfile . showProgram) $ compileProgram input
            _ -> putStrLn usage
            