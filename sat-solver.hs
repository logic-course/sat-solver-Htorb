module Main where

import System.IO
import System.Random
import Test.QuickCheck
import Formula
import Parser hiding (check)
import Utils

-- TODO
sat_solver :: Formula -> Bool
sat_solver phi = True

main :: IO Int
main = do
    eof <- hIsEOF stdin
    if eof
        then return 0
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let sat = sat_solver phi -- call the sat solver
                if sat
                    then putStrLn "1" -- write 1 if the formula is satisfiable
                    else putStrLn "0" -- write 0 if the formula is not satisfiable
                return 0