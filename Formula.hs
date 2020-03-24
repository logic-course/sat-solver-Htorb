module Formula where

type VarName = String
data Formula = T | F | Var VarName | Not Formula | And Formula Formula | Or Formula Formula | Implies Formula Formula | Iff Formula Formula deriving (Eq, Show)

infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, -->
(\/) = Or
(∨) = Or
(-->) = Implies

infixr 4 <-->
(<-->) = Iff

-- the following is a hard unsatisfiable formula
-- 15 variables
x_1_2 = Var "x12"
x_1_3 = Var "x13"
x_1_4 = Var "x14"
x_1_5 = Var "x15"
x_1_6 = Var "x16"
x_2_3 = Var "x23"
x_2_4 = Var "x24"
x_2_5 = Var "x25"
x_2_6 = Var "x26"
x_3_4 = Var "x34"
x_3_5 = Var "x35"
x_3_6 = Var "x36"
x_4_5 = Var "x45"
x_4_6 = Var "x46"
x_5_6 = Var "x56"

hard_unsat_formula = (Not (((x_1_2 ∧ (x_1_3 ∧ x_2_3)) ∨ ((x_1_2 ∧ (x_1_4 ∧ x_2_4)) ∨ ((x_1_2 ∧ (x_1_5 ∧ x_2_5)) ∨ ((x_1_2 ∧ (x_1_6 ∧ x_2_6)) ∨ ((x_1_3 ∧ (x_1_4 ∧ x_3_4)) ∨ ((x_1_3 ∧ (x_1_5 ∧ x_3_5)) ∨ ((x_1_3 ∧ (x_1_6 ∧ x_3_6)) ∨ ((x_1_4 ∧ (x_1_5 ∧ x_4_5)) ∨ ((x_1_4 ∧ (x_1_6 ∧ x_4_6)) ∨ ((x_1_5 ∧ (x_1_6 ∧ x_5_6)) ∨ ((x_2_3 ∧ (x_2_4 ∧ x_3_4)) ∨ ((x_2_3 ∧ (x_2_5 ∧ x_3_5)) ∨ ((x_2_3 ∧ (x_2_6 ∧ x_3_6)) ∨ ((x_2_4 ∧ (x_2_5 ∧ x_4_5)) ∨ ((x_2_4 ∧ (x_2_6 ∧ x_4_6)) ∨ ((x_2_5 ∧ (x_2_6 ∧ x_5_6)) ∨ ((x_3_4 ∧ (x_3_5 ∧ x_4_5)) ∨ ((x_3_4 ∧ (x_3_6 ∧ x_4_6)) ∨ ((x_3_5 ∧ (x_3_6 ∧ x_5_6)) ∨ (x_4_5 ∧ (x_4_6 ∧ x_5_6))))))))))))))))))))) ∨ (((Not x_1_2) ∧ ((Not x_1_3) ∧ (Not x_2_3))) ∨ (((Not x_1_2) ∧ ((Not x_1_4) ∧ (Not x_2_4))) ∨ (((Not x_1_2) ∧ ((Not x_1_5) ∧ (Not x_2_5))) ∨ (((Not x_1_2) ∧ ((Not x_1_6) ∧ (Not x_2_6))) ∨ (((Not x_1_3) ∧ ((Not x_1_4) ∧ (Not x_3_4))) ∨ (((Not x_1_3) ∧ ((Not x_1_5) ∧ (Not x_3_5))) ∨ (((Not x_1_3) ∧ ((Not x_1_6) ∧ (Not x_3_6))) ∨ (((Not x_1_4) ∧ ((Not x_1_5) ∧ (Not x_4_5))) ∨ (((Not x_1_4) ∧ ((Not x_1_6) ∧ (Not x_4_6))) ∨ (((Not x_1_5) ∧ ((Not x_1_6) ∧ (Not x_5_6))) ∨ (((Not x_2_3) ∧ ((Not x_2_4) ∧ (Not x_3_4))) ∨ (((Not x_2_3) ∧ ((Not x_2_5) ∧ (Not x_3_5))) ∨ (((Not x_2_3) ∧ ((Not x_2_6) ∧ (Not x_3_6))) ∨ (((Not x_2_4) ∧ ((Not x_2_5) ∧ (Not x_4_5))) ∨ (((Not x_2_4) ∧ ((Not x_2_6) ∧ (Not x_4_6))) ∨ (((Not x_2_5) ∧ ((Not x_2_6) ∧ (Not x_5_6))) ∨ (((Not x_3_4) ∧ ((Not x_3_5) ∧ (Not x_4_5))) ∨ (((Not x_3_4) ∧ ((Not x_3_6) ∧ (Not x_4_6))) ∨ (((Not x_3_5) ∧ ((Not x_3_6) ∧ (Not x_5_6))) ∨ ((Not x_4_5) ∧ ((Not x_4_6) ∧ (Not x_5_6))))))))))))))))))))))))