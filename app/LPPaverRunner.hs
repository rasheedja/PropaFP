module Main where

import MixedTypesNumPrelude
import Options.Applicative
import System.Directory
import PropaFP.Parsers.Smt
import PropaFP.Translators.DReal
import System.Process
import System.IO.Temp
import GHC.IO.Handle

data ProverOptions = ProverOptions
  {
    fileName :: String,
    dRealPath :: String
  }

proverOptions :: Parser ProverOptions
proverOptions = ProverOptions
  <$> strOption
    (
      long "file-path"
      <> short 'f'
      <> help "path to smt2 file to be checked"
      <> metavar "filePath"
    )
  <*> strOption
    (
      long "lppaver-path"
      <> short 'p'
      <> help "path to LPPaver executable"
      <> metavar "filePath"
    )

runLPPaver :: ProverOptions -> IO ()
runLPPaver (ProverOptions filePath lppaverPath) =
  do
    -- PATH needs to include folder containing FPTaylor binary after make
    -- symlink to the binary in somewhere like ~/.local/bin will NOT work reliably
    mFptaylorPath <- findExecutable "fptaylor"
    case mFptaylorPath of
      Nothing -> error "fptaylor executable not in path"
      Just fptaylorPath -> do
        mdRealInput <- parseVCToSolver filePath fptaylorPath formulaAndVarMapToDReal False
        case mdRealInput of
          Just dRealInput -> do
            (exitCode, output, errDetails) <- withSystemTempFile "lppaver.smt2" handleDRealFile
            putStrLn output
            return ()
            where
              handleDRealFile fPath fHandle =
                do
                  hPutStr fHandle dRealInput
                  _ <- hGetContents fHandle -- Ensure handler has finished writing before calling DReal
                  readProcessWithExitCode lppaverPath [fPath] []
          Nothing         -> error "Issue generating input for LPPaver"

main :: IO ()
main = 
  do 
    runLPPaver =<< execParser opts
    where
      opts = info (proverOptions <**> helper)
        ( fullDesc
        <> progDesc "todo"
        <> header "LPPaver - runner" )