module Main where

import Prelude
import TestFiles
import System.Directory
import PropaFP.Expression
import PropaFP.VarMap
import PropaFP.Parsers.Smt
import PropaFP.Translators.DReal
import PropaFP.Translators.MetiTarski
import System.Exit
import MixedTypesNumPrelude (ifThenElse)

main :: IO ()
main = do
  putStrLn "Testing dReal translator"
  testProverTranslator allTestFiles DReal []
  putStrLn "Testing MetiTarski translator"
  testProverTranslator allTestFiles MetiTarski unsupportedByMetiTarskiFiles
  exitSuccess

-- |Take a list of input files, a prover for which PropaFP provides a translator, and a list of files unsupported by the translator.
-- Test if PropaFP generates the same file as the one stored (currently under PropaFP/examples/testParent/proverFolderName/testName.proverExt)
testProverTranslator :: [(String, String)] -> SupportedProver -> [(String, String)] -> IO ()
testProverTranslator [] _ _ = putStrLn "All tests passed"
testProverTranslator (test@(testParent, testName) : tests) prover unsupportedTests = do
  mFptaylorPath <- findExecutable "fptaylor"
  currentDirectory <- getCurrentDirectory
  case mFptaylorPath of
    Nothing -> putStrLn "FPTaylor executable not found in PATH"
    Just fptaylorPath -> do
      let vcToProcess = currentDirectory ++ "/examples/" ++ testParent ++ "/why3smt/" ++ testName ++ ".smt2"
      let originalProcessedVCPath = currentDirectory ++  "/examples/" ++ testParent ++ "/" ++ getProverFolderName prover ++ "/" ++ testName ++ "." ++ getFileExtension prover
      if test `elem` unsupportedTests
        then do
          putStrLn ("Test skipped (unsupported): " ++ vcToProcess) 
          testProverTranslator tests prover unsupportedTests
        else do
          originalProcessedVC <- readFile originalProcessedVCPath
          mNewProcessedVC <- parseVCToSolver vcToProcess fptaylorPath (getTranslator prover) (getNegationStatus prover)
          case mNewProcessedVC of
            Just newProcessedVC -> 
              if newProcessedVC == originalProcessedVC
                then do
                  putStrLn ("Test passed: " ++ vcToProcess)
                  testProverTranslator tests prover unsupportedTests
                else do
                  putStrLn $ "Processing the following file for dReal: " ++ vcToProcess
                  putStrLn $ "Resulted in an output that differs from: " ++ originalProcessedVCPath
                  putStrLn $ "The incorrect output is:\n"
                  putStrLn newProcessedVC              
                  putStrLn $ "The correct output is:\n"
                  putStrLn originalProcessedVC
                  putStrLn ("Test failed: " ++ vcToProcess)
                  exitFailure
            Nothing         -> do
              putStrLn $ "Issue generating input for dReal using file: " ++ vcToProcess 
              exitFailure
              