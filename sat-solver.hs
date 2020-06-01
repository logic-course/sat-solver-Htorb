module Main where

import System.IO
import System.Random
import Test.QuickCheck
import Formula
import Parser hiding (check)
import Utils
import Data.List
import Data.List (nub, maximumBy)
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Arrow
import Debug.Trace

data Literal = Pos VarName | Neg VarName deriving (Eq, Show, Ord)
type SatSolver = Formula -> Bool
type Clause = [Literal]
type CNF = [Clause]

simplify :: Formula -> Formula

simplify T = T
simplify F = F
simplify (Var p) = Var p

simplify (Not T) = F
simplify (Not F) = T
simplify (Not (Not phi)) = simplify phi
simplify (Not phi) = Not (simplify phi)

simplify (And T phi) = simplify phi
simplify (And phi T) = simplify phi
simplify (And F _) = F
simplify (And _ F) = F
simplify (And phi psi) = And (simplify phi) (simplify psi)

simplify (Or T _) = T
simplify (Or _ T) = T
simplify (Or F phi) = simplify phi
simplify (Or phi F) = simplify phi
simplify (Or phi psi) = Or (simplify phi) (simplify psi)

simplify (Implies T phi) = simplify phi
simplify (Implies _ T) = T
simplify (Implies F _) = T
simplify (Implies phi F) = simplify (Not phi)
simplify (Implies phi psi) = Implies (simplify phi) (simplify psi)

simplify (Iff T phi) = simplify phi
simplify (Iff phi T) = simplify phi
simplify (Iff F phi) = simplify (Not phi)
simplify (Iff phi F) = simplify (Not phi)
simplify (Iff phi psi) = Iff (simplify phi) (simplify psi)

-- keep simplifying until no more simplifications are possible
deepSimplify :: Formula -> Formula
deepSimplify phi = go where
  psi = simplify phi
  go | phi == psi = phi
     | otherwise = deepSimplify psi

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Not T) = F
nnf (Not F) = T
nnf (Var p) = Var p
nnf (Not (Var p)) = Not $ Var p
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = nnf (Or (Not phi) psi)
nnf (Iff phi psi) = nnf (And (Implies phi psi) (Implies psi phi))
nnf (Not (Not phi)) = nnf phi
nnf (Not (And phi psi)) = nnf (Or (Not phi) (Not psi))
nnf (Not (Or phi psi)) = nnf (And (Not phi) (Not psi))
nnf (Not (Implies phi psi)) = nnf (And phi (Not psi))
nnf (Not (Iff phi psi)) = nnf (Or (And phi (Not psi)) (And (Not phi) psi))

cnf :: Formula -> CNF
cnf phi = go $ nnf phi where
  go T = []
  go F = [[]]
  go (Var x) = [[Pos x]]
  go (Not (Var x)) = [[Neg x]]
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = distribute (go phi) (go psi)

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos x) = Var x
  go2 (Neg x) = Not (Var x)

ecnf :: Formula -> CNF
ecnf phi = let (_, c_phi, forms) = go phi 0 in [[Pos $ show 0]] ++ forms where
  go :: Formula -> Int -> (Bool, Int, CNF)
  go T = op1arg T
  go F = op1arg F 
  go (Var x) = op1arg (Var x)
  go (Not phi) =  go $ phi --> F --todo
  go (And phi psi) = op2arg And phi psi
  go (Or phi psi) = op2arg Or phi psi
  go (Implies phi psi) = op2arg Implies phi psi
  go (Iff phi psi) = op2arg Iff phi psi

  op1arg :: Formula -> Int -> (Bool, Int, CNF)
  op1arg f ctr = (True, ctr, cnf f)

  op2arg :: (Formula -> Formula -> Formula) -> Formula -> Formula -> Int -> (Bool, Int, CNF)
  op2arg op psi1 psi2 ctr = let (simple1, c_psi1, f_psi1) = go psi1 (ctr + 1)
                                (simple2, c_psi2, f_psi2) = go psi2 c_psi1
                                var1 = if simple1 then cnf2formula f_psi1 else (Var $ show $ ctr + 1)
                                var2 = if simple2 then  cnf2formula f_psi2 else (Var $ show $ c_psi1)
                                new_f_psi1 = if simple1 then [] else f_psi1
                                new_f_psi2 = if simple2 then [] else f_psi2
                            in (False, c_psi2, (cnf $ (Var $ show ctr) <--> (op var1 var2)) ++ new_f_psi1 ++ new_f_psi2)

-- find all positive occurrences of a variable name
positiveLiterals :: Clause -> [VarName]
positiveLiterals ls = rmdups [p | Pos p <- ls]

-- find all negative occurrences of a variable name
negativeLiterals :: Clause -> [VarName]
negativeLiterals ls = rmdups [p | Neg p <- ls]

-- find all occurrences of a variable name
literals :: Clause -> [VarName]
literals ls = rmdups $ positiveLiterals ls ++ negativeLiterals ls

oneLiteral :: CNF -> CNF
-- oneLiteral lss = let new_lss = oneLiteralSingleStep lss
--                      res = if length new_lss == length lss 
--                             then lss
--                             else oneLiteral new_lss 
--                  in if res == [] then [[]] else res
oneLiteral lss = let singleElemClauses = filter (\ls -> (length ls) == 1) lss
                     singleLiterals = map (\(l:_) -> l) singleElemClauses
                 in oneLiteralSingleStep lss singleLiterals

oneLiteralSingleStep :: CNF -> [Literal] -> CNF
oneLiteralSingleStep lss [] = lss
oneLiteralSingleStep lss (x:xs) = 
    let removed_l = filter (\ls -> not $ elem x ls) lss
        empty_clauses_removed = filter (/= []) removed_l
        opposite_l_removed = map (\ls -> if elem (opposite x) ls then filter (/= (opposite x)) ls else ls) empty_clauses_removed
    in if elem [] opposite_l_removed then [[]] else oneLiteralSingleStep opposite_l_removed xs 
    where 
        opposite :: Literal -> Literal
        opposite (Pos p) = Neg p
        opposite (Neg p) = Pos p


removeTautologies :: CNF -> CNF
removeTautologies = filter (\ls -> (length $ literals ls) == (length $ positiveLiterals ls) + (length $ negativeLiterals ls))

affirmativeNegative :: CNF -> CNF
affirmativeNegative lss = let pl = rmdups (concat (map positiveLiterals lss))
                              nl = rmdups (concat (map negativeLiterals lss))
                              symDiff = (pl \\ nl) ++ (nl \\ pl)
                          in affirmativeNegativeSingleStep lss symDiff

affirmativeNegativeSingleStep :: CNF -> [VarName] -> CNF
affirmativeNegativeSingleStep lss [] = lss
affirmativeNegativeSingleStep lss (x:xs) = 
    let newLss = filter (\ls -> not $ elem (Pos x) ls) $ filter (\ls -> not $ elem (Neg x) ls) lss
    in affirmativeNegativeSingleStep newLss xs

pickFirstVar :: CNF -> VarName
pickFirstVar ((x:_):_) = case x of 
                            Neg v -> v
                            Pos v -> v

type Score = [Literal] -> Double

unwrapList :: [Literal] -> [VarName]
unwrapList = map unwrap

unwrap :: Literal -> VarName
unwrap (Pos p) = p
unwrap (Neg p) = p

pick :: Score -> CNF -> VarName
pick score lss = maximalFromMap $ createMapWithScore score lss
    where
        maximalFromMap :: Map VarName Double -> VarName 
        maximalFromMap mmap = fst . maximumBy (compare `on` snd) $ Map.toList mmap 
        
        createMapWithScore :: Score -> CNF -> Map VarName Double
        createMapWithScore score = foldl (\acls ls -> foldl (\acl l -> Map.insertWith (+) (unwrap l) (score ls) acl) acls ls) Map.empty

pickJW :: CNF -> VarName
pickJW = pick scoreJW 
    where 
        scoreJW :: Score
        scoreJW ls = (1/2::Double) ^^ (length ls)

pickMAXO :: CNF -> VarName
pickMAXO = pick scoreMAXO 
    where 
        scoreMAXO :: Score
        scoreMAXO ls = 1

-- pickMAXO :: CNF -> VarName
-- pickMAXO lss = mostCommon $ concat $ map unwrapList lss
--     where
--         --https://stackoverflow.com/questions/13833017/haskell-most-frequent-value
--         mostCommon list = fst . maximumBy (compare `on` snd) $ map (head &&& length) . group . sort $ list 

        

        
 

clausesWithLiteral :: CNF -> Literal -> CNF
clausesWithLiteral lss p = foldl (\ac ls -> if elem p ls then ac ++ [(delete p ls)] else ac) [] lss

-- resolution :: CNF -> CNF
-- resolution lss = let p = pickFirstVar lss
--                      lss_pos = clausesWithLiteral lss (Pos p)
--                      lss_neg = clausesWithLiteral lss (Neg p)
--                      new_clauses = distribute lss_pos lss_neg
--                      old_clauses = filter (\ls -> not (elem (Pos p) ls || elem (Neg p) ls)) lss in new_clauses ++ old_clauses
dpll :: VarName -> Bool -> CNF -> CNF
dpll p value lss = let lss_with_false_variable_valuation = clausesWithLiteral lss $ if value then (Neg p) else (Pos p)
                       other_clauses = filter (\ls -> not (elem (Pos p) ls || elem (Neg p) ls)) lss 
                   in other_clauses ++ lss_with_false_variable_valuation
            
loopDP :: CNF -> Bool
loopDP [] = True
loopDP lss | [] `elem` lss = False 
loopDP lss =
  let lss' = rmdups . map rmdups . affirmativeNegative . oneLiteral . removeTautologies $ lss in
    if lss == lss'
      then let var = pickJW lss in (loopDP $ dpll var True lss) || (loopDP $ dpll var False lss)
      else loopDP lss'

sat_solver :: SatSolver
sat_solver =  loopDP . ecnf . deepSimplify 




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



-----------------------------------------------------------------------------------------------------


-- main = do 
--   quickCheckWith (stdArgs {maxSize = 5}) prop_ecnf
--   quickCheck prop_oneLiteral
--   quickCheck prop_affirmativeNegative
--   quickCheckWith (stdArgs {maxSize = 10}) prop_DP
--   quickCheck prop_DP2


instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ map Var ["p", "q", "r", "s", "t"] ++ [T, F]

      f size = frequency [
        (1, fmap Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]

-- finds all variables occurring in the formula (sorted, without duplicates)
variables :: Formula -> [VarName]
variables = rmdups . go where
  go T = []
  go F = []
  go (Var x) = [x]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi

-- truth valuations
type Valuation = VarName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Var x) rho = rho x
eval (Not phi) rho = not $ eval phi rho
eval (And phi psi) rho = eval phi rho && eval psi rho
eval (Or phi psi) rho = eval phi rho || eval psi rho
eval (Implies phi psi) rho = not (eval phi rho) || eval psi rho
eval (Iff phi psi) rho = eval phi rho == eval psi rho

-- updating a truth valuation
extend :: Valuation -> VarName -> Bool -> Valuation
extend rho x v y
  | x == y = v
  | otherwise = rho y

-- the list of all valuations on a given list of variables
valuations :: [VarName] -> [Valuation]
valuations [] = [\_ -> False] -- any initial valuation would do
valuations (x : xs) = concat [[extend rho x True, extend rho x False] | rho <- valuations xs]

-- satisfiability checker based on truth tables
satisfiable :: Formula -> Bool
satisfiable phi = or [eval phi rho | rho <- valuations (variables phi)]


equiSatisfiable :: Formula -> Formula -> Bool
equiSatisfiable phi psi = satisfiable phi == satisfiable psi


-- test for ecnf
prop_ecnf :: Formula -> Bool
prop_ecnf phi = equiSatisfiable phi (cnf2formula $ ecnf phi)

test_solver :: SatSolver -> Bool
test_solver solver = and $ map solver satisfiableFormulas ++ map (not . solver) unsatisfiableFormulas

-- the DP SAT solver
satDP :: SatSolver
satDP = loopDP . ecnf . deepSimplify 


-- correctness test
prop_oneLiteral :: Bool
prop_oneLiteral =
  oneLiteral [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] ==
    [[Neg "q",Pos "r",Neg "r"],[Neg "q"],[Pos "q",Pos "r",Pos "s"]] &&
  oneLiteral [[Pos "p2"],[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Pos "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
   [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  oneLiteral [[Pos "p0"], [Pos "q"],[Neg "p0",Pos "s"],[Neg "p0"]] == [[]]

prop_affirmativeNegative :: Bool
prop_affirmativeNegative =
  affirmativeNegative [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]]

-- some examples of formulas
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"

satisfiableFormulas = [p /\ q /\ s /\ p, T, p, Not p, (p \/ q /\ r) /\ (Not p \/ Not r), (p \/ q) /\ (Not p \/ Not q)]
unsatisfiableFormulas = [p /\ q /\ s /\ Not p, T /\ F, F, (p \/ q /\ r) /\ Not p /\ Not r, (p <--> q) /\ (q <--> r) /\ (r <--> s) /\ (s <--> Not p)]

-- tests on random formulas
prop_DP :: Formula -> Bool
prop_DP phi = -- unsafePerformIO (do print "Checking:"; print phi; return True) `seq`
  satDP phi == satisfiable phi

-- tests on fixed formulas
prop_DP2 :: Bool
prop_DP2 = test_solver satDP

