theory ExerciseProgProf
imports Complex_Main
begin

(*simplify the naming *)
declare [[names_short]]

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02: "add m 0 = m"
apply(induction m)
apply(auto)
done

thm add_02

lemma add_comm: "add x (add y z) = add (add x y) z"
  apply (induction x)
  apply (auto) 
  done

lemma add_assoc0[simp]: "add m (Suc n) = Suc (add m n)"
apply (induction m)
apply (auto)
done 

lemma add_assoc: "add m n = add n m"
  apply (induction m) 
  apply (induction n)
  apply (auto)
  done  

fun double :: "nat \<Rightarrow> nat" where 
"double 0 = 0" | "double (Suc m) = add (Suc (Suc 0) ) (double m)" 

value "double (2::nat)"

lemma double_0: "double m = add m m"
apply (induction m)
apply (auto)
done 


(* List part *)
fun app:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"app Nil ys = ys" | "app (Cons x xs) ys = Cons x (app xs ys)"

lemma [simp]: "app xs ys = xs @ ys "
  apply (induction xs) 
  apply (auto)
  done 

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs) 
  apply (auto)
done 

lemma app_assoc [simp]: "app xs (app ys zs) = app (app xs ys ) zs"
  apply (induction xs)
  apply auto 
done 


lemma app_rev [simp]: "rev (app xs ys) = app (rev ys) (rev xs) "
  apply (induction xs)
  apply (auto) 
done 


fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where 
"count i (Cons x xs) = (if i = x then Suc (count i xs) else (count i xs)) " | "count i Nil = 0" 

fun length :: "'a list \<Rightarrow> nat " where 
"length (Cons x xs) = Suc (length xs)" | "length Nil = 0"

lemma count_lessThenLength : "count x xs \<le> length xs"
  apply (induction xs)
  apply (auto )
  done 

fun snoc :: "'a list \<Rightarrow>'a \<Rightarrow> 'a list " where 
"snoc Nil elem = (Cons elem Nil)" | "snoc (Cons v vs) el = Cons v (snoc vs el)"

fun reverse :: "'a list \<Rightarrow> 'a list "  where 
"reverse (Cons v vs) = snoc (reverse vs)  v" | "reverse Nil = Nil"

lemma snoc_app [simp] : "snoc xs x = app xs (Cons x Nil)"
  apply (induction xs) 
  apply (auto)
  done 


(*This is a hack*)
lemma reverse_rev [simp]: "reverse xs = rev xs"
  apply (induction xs)
  apply (auto)
  done

lemma reverse_reverse : "reverse (reverse xs) = xs"
  apply (induction xs)
  apply (auto)
done 

fun sum_upto :: "nat\<Rightarrow> nat" where 
"sum_upto (Suc x) = (Suc x) + (sum_upto x)" | "sum_upto 0 = 0"

lemma sum_upto_short : "sum_upto n = n * (n +1 ) div 2 "
  apply (induction n)
  apply (auto )
  done 

(* Tree definition *)

datatype 'a tree = Tip | Node "'a tree"  'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where 
"mirror Tip = Tip" | 
"mirror (Node l a r ) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t ) = t" 
  apply (induction t)
  apply (auto)
  done 

fun contents :: "'a tree \<Rightarrow> 'a list" where 
"contents Tip = Nil" |
"contents (Node l a r ) = Cons a (app (contents l) (contents r))"


fun sum_tree :: "nat tree \<Rightarrow> nat" where 
"sum_tree Tip = 0" |
"sum_tree (Node l a r ) = a + (sum_tree l) + (sum_tree r)"

fun sum_list :: "nat list \<Rightarrow> nat" where 
"sum_list Nil = 0"| 
"sum_list (Cons x xs) = x + sum_list xs"

lemma sum_list_app [simp] :"sum_list l1 + sum_list l2 = sum_list (app l1 l2) "
  apply (induction l1)
  apply (induction l2)
  apply (auto)
done 

lemma sum_list_contents_eq_sum_tree: "sum_tree t = sum_list ( contents t )"
  apply (induction t rule: contents.induct)
  apply (auto)
  done 

datatype 'a tree2 = Tip 'a | Node "'a tree2"  'a "'a tree2"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list " where
"pre_order (Tip v) = Cons v Nil" | 
"pre_order (Node l a r) = (Cons a (app (pre_order l) (pre_order r)))"

fun post_order :: "'a tree2 \<Rightarrow> 'a list " where 
"post_order (Tip v) = Cons v Nil" |
"post_order (Node l a r ) = snoc (app (post_order l) (post_order r)) a"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where 
"mirror2 (Tip v) = Tip v" | "mirror2 (Node l a r) = Node (mirror2 r) a (mirror2 l) "

lemma [simp] : "mirror2 (mirror2 t)= t"
  apply (induction t)
  apply (auto)
done 

lemma app_nil2 [simp] : "app (Cons x Nil) (Cons y l2) = app (Cons x (Cons y Nil)) l2"
  apply (induction l2)
  apply (auto)
done 

lemma "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t )
  apply (auto)  
  done

(* Intersperse *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"intersperse e []       = []" | 
"intersperse e (x # []) = x # []" |
"intersperse e (x # xs) = x # e # (intersperse e xs)"



lemma "(map f (intersperse a xs)) = (intersperse (f a) (map f xs))"
  apply (induction xs rule:intersperse.induct)
  apply auto
done

(* rev *)
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
"itrev []       ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"


lemma "itrev xs ys = rev xs @ ys" 
  apply (induction xs arbitrary:ys)
  apply auto
  done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"itadd (Suc m) n = itadd m (Suc n)" | 
"itadd 0 n = n"

lemma "itadd m n = add m n" 
  apply (induction m arbitrary: n)
  apply auto
  done

(* No Elem Tree*)
datatype tree0 = Tip | Node tree0 tree0

fun nodes:: "tree0 \<Rightarrow> nat" where 
"nodes Tip = 1" | 
"nodes (Node x y) = 1 + (nodes x) + (nodes y)"


fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0 " where 
"explode 0 t = t"| 
"explode (Suc n) t = Node (explode n t) (explode n t)"

(*lemma explode_suc : "nodes (explode (Suc n) t ) = nodes (explode n (Node t t ))"
  apply auto 
  done 
*)


lemma explode_expand: "explode (Suc n) t = Node (explode n t) (explode n t)"
 
  apply (induction n)
  apply auto
  done 

lemma "nodes(explode (Suc n) t ) = 1 + 2 * nodes (explode n t)"
  apply auto 
  done 


lemma "nodes (explode n t) =  (2^n - 1) + (2 ^ n) * nodes t" 
  apply (induction n )
  apply auto 
  done 


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
"evalp is i = eval (build_exp is) i"


end