module Utils where

import Data.List
import Test.QuickCheck

rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort

checkAll :: Testable prop => [prop] -> IO ()
checkAll [] = return ()
checkAll (p:ps) = do quickCheck p; checkAll ps

-- find all ways of joining the lists (c.f. example below)
distribute :: [[a]] -> [[a]] -> [[a]]
distribute xss yss = go xss yss yss where
  go [] _ _ = []
  go (_:xss) yss [] = go xss yss yss
  go (xs:xss) yss (ys:yss') = (xs ++ ys) : go (xs:xss) yss yss'

prop_distribute :: Bool
prop_distribute = distribute [[1, 2], [3, 4]] [[5, 6], [7]] == [[1, 2, 5, 6], [1, 2, 7], [3, 4, 5, 6], [3, 4, 7]]
