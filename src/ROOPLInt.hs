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

-- Following methods is based on work from Jana https://github.com/mbudde/jana
-- `RunOpt`, `Options`, `usage`, `parseArgs`
-- `assertInputMethod`, `checkFlags` and `setOption`
data RunOpt = Compile
            | Interpret
            | Invert

data Options =
    Options {
        runOpt :: RunOpt,
        timeOut :: Int,
        output :: String
    }

-- | Default options
defaultOpts :: Options
defaultOpts =
    Options {
        runOpt = Interpret,
        timeOut = -1,
        output = ""
    }

-- | Common usage string
usage :: String
usage = "usage: ROOPLInt [-i | -c | -tN] <input>.rplpp [-o<output>]\n\
        \options:\n\
        \ -i:           invert program\n\
        \ -c:           compile program\n\
        \ -o<FILENAME>: output compiled program (only when -c or -i is used)\n\
        \ -tN:          timeout after N seconds"

-- | Parses and asserting input arguments
parseArgs :: IO (Maybe (String, Options))
parseArgs = do
    args <- getArgs
    when (null args) (putStrLn ("Supply input filename.\n" ++ usage) >> exitFailure)
    let (flgs, fname) = partition (\a -> head a == '-' && length a > 1) args
     in do
         assertInputMethod fname
         case checkFlags flgs of
            Left err -> putStrLn err >> return Nothing
            Right opts -> return $ Just (head fname, opts)

-- | Asserts that only one input method, i.e. filename or stdin, is defined
assertInputMethod :: [String] -> IO ()
assertInputMethod fname = do
    when (null fname) (putStrLn ("No file or input method specified. Specify one file or '-' to use stdin\n" ++ usage) >> exitFailure)
    when (length fname > 1) (putStrLn ("More than one input method specified. Specify one file or '-' to use stdin\n" ++ usage) >> exitFailure)

-- | Check input list for valid arguments
checkFlags :: [String] -> Either Error Options
checkFlags = foldM setOption defaultOpts

-- | Sets fields in the `Options` record
setOption :: Options -> String -> Either Error Options
setOption opts "-i" = return $ opts { runOpt = Invert }
setOption opts "-c" = return $ opts { runOpt = Compile }
setOption opts ('-':'o':filename) = return $ opts { output = filename }
setOption opts ('-':'t':time) =
    case reads time of
        [(val,"")] -> return $ opts { timeOut = val * 1000000 } -- convert to seconds
        _          -> Left "Non-integer provided in the -t option"
setOption _ f = Left $ "invalid option: " ++ f

-- | Gets file content from file or stdin
loadContent :: String -> IO String
loadContent "-" = getContents
loadContent fname = do
    handle <- openFile fname ReadMode
    hGetContents handle

-- | Writes output to file or stdout
writeOutput :: String -> String -> String -> IO ()
writeOutput "-" "" content = putStrLn content
writeOutput defaultName "" content =
    let fname = head (splitOn "." defaultName) ++ "-inverted.rplpp"
     in writeFile fname content
writeOutput _ outfile content = writeFile outfile content

-- | Backend parsing and analysis
parseAndAnalysis :: String -> Except Error (SProgram, SAState)
parseAndAnalysis s =
    parseString s
    >>= classAnalysis
    >>= scopeAnalysis
    >>= typeCheck

-- | Interprets the parsed and analyzed program
interpretProgram :: String -> Either Error String
interpretProgram s =
    runExcept $
    parseAndAnalysis s
    >>= interpret

-- | Inverts the input program
invertProgram :: String -> Either Error String
invertProgram s =
    runExcept $
    parseAndAnalysis s
    >>= invert

-- | Compiles the parsed and analyzed program
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
                loadContent file >>= \input -> do
                    res <- timeout (timeOut opts) (return $ interpretProgram input)
                    case res of
                        Nothing -> exitWith $ ExitFailure 100
                        Just res' -> either (\err -> putStrLn err >> exitWith (ExitFailure 1)) putStrLn res'
            -- Invert
            Just (file, Options { runOpt = Invert, output = outfile }) ->
                loadContent file >>= \input ->
                    either (\err -> putStrLn err >> exitWith (ExitFailure 1)) (writeOutput file outfile) $ invertProgram input
            -- Compile
            Just (file, Options { runOpt = Compile, output = outfile }) ->
                loadContent file >>= \input ->
                    either (\err -> putStrLn err >> exitWith (ExitFailure 1)) (writeOutput file outfile . showProgram) $ compileProgram input
            _ -> putStrLn usage
            