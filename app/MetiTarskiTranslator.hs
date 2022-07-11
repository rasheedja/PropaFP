module Main where

import MixedTypesNumPrelude
import Options.Applicative
import System.Directory
import PropaFP.Parsers.Smt
import PropaFP.Translators.MetiTarski

data ProverOptions = ProverOptions
  {
    fileName :: String,
    targetName :: String
  }

proverOptions :: Parser ProverOptions
proverOptions = ProverOptions
  <$> strOption
    (
      long "file-path"
      <> short 'f'
      <> help "SMT2 file to be checked"
      <> metavar "filePath"
    )
  <*> strOption
    (
      long "target-path"
      <> short 't'
      <> help "location to write MetiTarski file"
      <> metavar "targetPath"
    )

runMetiTarskiTranslator :: ProverOptions -> IO ()
runMetiTarskiTranslator (ProverOptions filePath targetPath) =
  do
    -- PATH needs to include folder containing FPTaylor binary after make
    -- symlink to the binary in somewhere like ~/.local/bin will NOT work reliably
    mFptaylorPath <- findExecutable "fptaylor"
    case mFptaylorPath of
      Nothing -> putStrLn "FPTaylor executable not found in path"
      Just fptaylorPath -> do
        mMetiTarskiInput <- parseVCToSolver filePath fptaylorPath formulaAndVarMapToMetiTarski True -- Negate the VC, MetiTarski does not give unsat, only sat or gave up, so make MetiTarski prove the contradiction
        case mMetiTarskiInput of
          Just metiTarskiInput -> writeFile targetPath metiTarskiInput
          Nothing         -> error "Issue generating input for MetiTarski"

main :: IO ()
main = 
  do 
    runMetiTarskiTranslator =<< execParser opts
    where
      opts = info (proverOptions <**> helper)
        ( fullDesc
        <> progDesc "todo"
        <> header "MetiTarski - translator" )
