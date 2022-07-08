module Lib
    ( someFunc
    ) where

import MixedTypesNumPrelude
import System.IO

someFunc :: IO ()
someFunc = putStrLn "someFunc"
