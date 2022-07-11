module Main where

import MixedTypesNumPrelude
import Options.Applicative
import System.Directory
import PropaFP.Parsers.Smt
import PropaFP.Expression

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
      <> help "SMT2 file to be prettified"
      <> metavar "filePath"
    )
  <*> strOption
    (
      long "target-path"
      <> short 't'
      <> help "location to write prettified file"
      <> metavar "targetPath"
    )

runDRealTranslator :: ProverOptions -> IO ()
runDRealTranslator (ProverOptions filePath targetPath) =
  do
    -- PATH needs to include folder containing FPTaylor binary after make
    -- symlink to the binary in somewhere like ~/.local/bin will NOT work reliably
    mFptaylorPath <- findExecutable "fptaylor"
    case mFptaylorPath of
      Nothing -> putStrLn "FPTaylor executable not found in path"
      Just fptaylorPath -> do
        mVC <- parseVCToF filePath fptaylorPath
        case mVC of
          Just (vc, vm) -> writeFile targetPath (prettyShowVC vc vm)
          Nothing         -> error "Issue processing SMT2 file"

main :: IO ()
main = 
  do 
    runDRealTranslator =<< execParser opts
    where
      opts = info (proverOptions <**> helper)
        ( fullDesc
        <> progDesc "todo"
        <> header "SMT2 Prettifier" )
