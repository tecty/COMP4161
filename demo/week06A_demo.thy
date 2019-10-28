theory week06A_demo imports Main begin

\<comment> \<open> ----------------------------------------------------------------\<close>

text \<open>a recursive data type: \<close>
datatype ('a,'b) tree = Tip | Node "('a,'b) tree" 'b "('a,'b) tree"

print_theorems

text \<open> distinctness of constructors automatic: \<close>
lemma "Tip ~= Node l x r" by simp

text \<open> case syntax, case distinction manual \<close>
lemma "(1::nat) \<le> (case t of Tip \<Rightarrow> 1 | Node l x r \<Rightarrow> x+1)"
  apply(case_tac t)
  apply auto
  done

text \<open> partial cases and dummy patterns: \<close>
term "case t of Node _ b _ => b" 

text \<open> partial case maps to 'undefined': \<close>
lemma "(case Tip of Node _ _ _ => 0) = undefined" by simp

text \<open> nested case and default pattern: \<close>
term "case t of Node (Node _ _ _) x Tip => 0 | _ => 1"


text \<open> infinitely branching: \<close>
datatype 'a inftree = Tp | Nd 'a "nat \<Rightarrow> 'a inftree"

text \<open> mutually recursive \<close> 
datatype 
  ty = Integer | Real | RefT ref
  and
  ref = Class | Array ty







\<comment> \<open> ----------------------------------------------------------------\<close>

text \<open> primitive recursion \<close>

primrec
  app :: "'a list => 'a list => 'a list"
where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"

print_theorems

primrec
  rv :: "'a list => 'a list"
where
  "rv [] = []" |
  "rv (x#xs) = app (rv xs) [x]"
print_theorems

text \<open> on trees \<close>
primrec
  mirror :: "('a,'b) tree => ('a,'b) tree"
where
  "mirror Tip = Tip" |
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"

print_theorems


text \<open> mutual recursion \<close>
primrec
  has_int :: "ty \<Rightarrow> bool" and
  has_int_ref :: "ref \<Rightarrow> bool"
where
  "has_int Integer       = True" |
  "has_int Real          = False" |
  "has_int (RefT T)      = has_int_ref T" |

  "has_int_ref Class     = False" |
  "has_int_ref (Array T) = has_int T"



\<comment> \<open> ----------------------------------------------------------------\<close>

text \<open> structural induction \<close>

text \<open> discovering lemmas needed to prove a theorem \<close>

lemma app_nil: "app xs [] = xs"
  apply (induct xs)
   apply auto
  done

lemma app_app: "app (app xs ys ) zs = app xs (app ys zs)"
  apply (induct xs) 
   apply auto 
  done


lemma rv_app: "rv (app xs ys) = app (rv ys) (rv xs)"
  apply (induct xs arbitrary: ys)
   apply (simp add: app_nil)
  apply (auto simp: app_app)
  done

theorem rv_rv: "rv (rv xs) = xs"
  apply (induct xs)
  apply (auto simp:rv_app)
  done

text \<open> induction heuristics \<close>

primrec
  itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "itrev [] ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_rev_app: "itrev xs ys = rev xs @ ys"
  apply (induct xs arbitrary:ys)
   apply auto
  done

lemma "itrev xs [] = rev xs"
  apply (induct xs)
  apply simp
  apply (clarsimp simp: itrev_rev_app)
  done




\<comment> \<open> ----------------------------------------------------------------\<close>

primrec
  lsum :: "nat list \<Rightarrow> nat"
where
  "lsum [] = 0" |
  "lsum (x#xs) = x + lsum xs"

lemma lsm_app:"lsum (xs @ ys) = lsum xs + lsum ys"
  apply (induct xs arbitrary:ys)
   apply auto 
  done 

lemma 
  "2 * lsum [0 ..< Suc n] = n * (n + 1)"
  apply (induct n)
   apply (auto simp:lsm_app)
  done

lemma 
  "lsum (replicate n a) = n * a"
  apply (induct n)
   apply simp_all
  done

text \<open> tail recursive version: \<close>

primrec
  lsumT :: "nat list \<Rightarrow> nat \<Rightarrow> nat" 
where
  "lsumT [] s = s" | 
  "lsumT (x # xs) s = lsumT xs x+s"
  
lemma lsum_a:
  "lsumT xs x = x + lsum xs"
  apply (induct xs arbitrary: x)
   apply auto
  done

lemma lsum_correct:
  "lsumT xs 0 = lsum xs"
  apply (auto simp:lsum_a)
  done
  

end
