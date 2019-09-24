theory Ch2ProfTree0
  imports Main
begin

(* arithmetic Example *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where 
"eval Var x = x" | 
"eval (Const c) x = c" | 
"eval (Add e1 e2) x = eval e1 x + eval e2 x" | 
"eval (Mult e1 e2) x = eval e1 x * eval e2 x"

fun build_exp:: "int list \<Rightarrow> exp" where 
"build_exp (x #xs) = Add (Const x) (Mult Var (build_exp xs))" | 
"build_exp [] = Const 0"

fun evalp :: "int list  \<Rightarrow> int \<Rightarrow> int" where 
"evalp xs i = eval (build_exp xs) i"

fun array_add :: "int list \<Rightarrow> int list \<Rightarrow> int list " where 
"array_add (x # xs ) (y # ys) = (x+ y) # (array_add xs ys)"|
"array_add xs [] = xs" | 
"array_add [] ys = ys"

fun array_times :: "int list \<Rightarrow> int list \<Rightarrow> int list" where 
"array_times (x # xs ) (y # ys) = x * y # (array_add (array_times xs (y#ys)) (array_times [x] ys))" | 
"array_times _ _ = []"

value "array_times [1,1] [1,-1]"

fun coeffs :: "exp \<Rightarrow> int list" where 
"coeffs Var = [0,1]" |
"coeffs (Const c ) = [c]" |
"coeffs (Add e1 e2) = array_add (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = array_times (coeffs e1) (coeffs e2)"


value "evalp [0, 1] (- 1)"

value "coeffs Var "
lemma "eval (build_exp (array_add (coeffs e1) (coeffs e2))) x = eval e1 x + eval e2 x"
  
  oops
lemma "eval (build_exp (array_times (coeffs e1) (coeffs e2))) x = eval e1 x * eval e2 x"
  oops


lemma "evalp (coeffs e) x = eval e x "
  apply (induction rule:coeffs.induct)
  apply auto
  oops
end