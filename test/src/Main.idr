module Main

import Data.String.Builder

import Data.String.Builder.Test

main : IO ()
main = do
    putStrLn $ build numbers
    putStrLn $ build alphabet
