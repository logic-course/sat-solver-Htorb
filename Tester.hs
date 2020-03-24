module Main where

import Parser
import System.IO
import System.Exit

main :: IO Int
main = do
    phi <- getLine
    solution <- getLine
    result <- getLine

    --putStrLn $ "phi: " ++ phi
    --putStrLn $ "solution: " ++ solution
    --putStrLn $ "result: " ++ result

    if solution == result
        then do --putStrLn "OK"
                return 0
        else do --putStrLn "NOPE"
                exitWith $ ExitFailure 1