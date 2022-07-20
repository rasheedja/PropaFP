module Main where

import MixedTypesNumPrelude
import Options.Applicative
import System.Directory
import PropaFP.Parsers.Smt
import PropaFP.Translators.MetiTarski
import System.Process
import System.IO.Temp
import GHC.IO.Handle
import GHC.SysTools (isContainedIn)

data ProverOptions = ProverOptions
  {
    filePath :: String,
    metiTarskiPath :: String,
    convertForWhy3 :: Bool
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
      long "metitarski-path"
      <> short 'p'
      <> help "path to MetiTarski executable"
      <> metavar "filePath"
    )
  <*> switch
    (
      long "convert-for-why3"
      <> short 'c'
      <> help "Converts MetiTarski output to SMT style output, so Why3 can understand the output (Theorem turns into 'unsat', anything else turns into 'unknown')"
    )
    
runMetiTarski :: ProverOptions -> IO ()
runMetiTarski (ProverOptions filePath' metiTarskiPath' convertForWhy3') =
  do
    -- PATH needs to include folder containing FPTaylor binary after make
    -- symlink to the binary in somewhere like ~/.local/bin will NOT work reliably
    mFptaylorPath <- findExecutable "fptaylor"
    case mFptaylorPath of
      Nothing -> error "fptaylor executable not in path"
      Just fptaylorPath -> do
        mMetiTarskiInput <- parseVCToSolver filePath' fptaylorPath formulaAndVarMapToMetiTarski True -- Negate the VC, MetiTarski does not give unsat, only sat or gave up, so make MetiTarski prove the contradiction
        case mMetiTarskiInput of
          Just metiTarskiInput -> do
            (exitCode, output, errDetails) <- withSystemTempFile "metitarski.tptp" handleMetiTarskiFile
            if convertForWhy3' then putStrLn (convertOutputToSMT output) else putStrLn output
            return ()
            where
              convertOutputToSMT outputToConvert = 
                if "Theorem" `isContainedIn` outputToConvert
                  then "unsat"
                  else "unknown"

              handleMetiTarskiFile fPath fHandle =
                do
                  hPutStr fHandle metiTarskiInput
                  _ <- hGetContents fHandle -- Ensure handler has finished writing before calling MetiTarski
                  readProcessWithExitCode metiTarskiPath' ["--autoIncludeSuperExtended", fPath] []
          Nothing         -> error "Issue generating input for MetiTarski"

main :: IO ()
main = 
  do 
    runMetiTarski =<< execParser opts
    where
      opts = info (proverOptions <**> helper)
        ( fullDesc
        <> progDesc "todo"
        <> header "MetiTarski - runner" )