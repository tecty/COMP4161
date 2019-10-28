theory week04B_demo imports Main begin

\<comment> \<open>------------------------------------------------------------------\<close>

text \<open>implicit backtracking\<close>
lemma "\<lbrakk>P \<and> Q; R \<and> S\<rbrakk> \<Longrightarrow> S"
  (* doesn't work -- picks the wrong assumption 
  apply(erule conjE)
  apply assumption  *)
  apply(erule conjE, assumption)
  done

text \<open>do (n) assumption steps\<close>
lemma "\<lbrakk>P \<and> Q\<rbrakk> \<Longrightarrow> P"
  apply(erule (1) conjE)
  done

text \<open>'by' does extra assumption steps implicitly\<close>
lemma "\<lbrakk>P \<and> Q\<rbrakk> \<Longrightarrow> P"
  by(erule conjE)

text \<open>more automation\<close>

\<comment> \<open>clarsimp: repeated clarify and simp\<close>
lemma "ys = []  \<Longrightarrow> \<forall>xs. xs @ ys = []"
  apply clarsimp
  oops

\<comment> \<open>auto: simplification, classical reasoning, more\<close>
lemma "(\<exists>u::nat. x=y+u) \<longrightarrow> a*(b+c)+y \<le> x + a*b+a*c" thm add_mult_distrib2
  apply (auto simp add: add_mult_distrib2)
  done

\<comment> \<open>limit auto (and any other tactic) to first [n] goals\<close>
lemma "(True \<and> True)"
  apply(rule conjI)
   apply(auto)[1]
  apply(rule TrueI)
  done

\<comment> \<open>also try: fastforce and force\<close>


print_simpset


text \<open>simplification with assumptions, more control:\<close>

lemma "\<forall>x. f x = g x \<and> g x = f x \<Longrightarrow> f [] = f [] @ []"
  \<comment> \<open>would diverge:\<close>
  (* 
  apply(simp)
  *)
  apply(simp (no_asm))
  done

\<comment> \<open>------------------------------------------------------\<close>

\<comment> \<open>let expressions\<close>

lemma "let a = f x in g a = x"
  apply (simp add: Let_def)
  oops

thm Let_def

term "let a = f x in g a"
term "(let a = f x in g (a + a)) = (Let (f x) (\<lambda>a. g (a + a)))"
\<comment> \<open>------------------------------------------------------\<close>

\<comment> \<open>splitting case: manually\<close>

lemma "(case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> x) = x"
  apply (simp only: split: nat.splits)
  apply simp
  done

\<comment> \<open>splitting if: automatic in conclusion\<close>

lemma "\<lbrakk> P; Q \<rbrakk> \<Longrightarrow> (if x then A else B) = z"
  apply simp
  oops


thm if_splits 
thm if_split_asm

lemma "\<lbrakk> (if x then A else B) = z; Q \<rbrakk> \<Longrightarrow> P" 
   apply(simp split: if_splits) (*
   apply (simp split: if_split_asm)*)
  oops

lemma " ((if x then A else B) =z) \<longrightarrow> (z=A\<or>z=B)" 
  apply simp
done

thm conj_cong

lemma "A \<and> (A \<longrightarrow> B)"
  apply (simp cong: conj_cong)
  oops

thm if_cong

lemma "\<lbrakk> (if x then x \<longrightarrow> z else B) = z; Q \<rbrakk> \<Longrightarrow> P"
  apply (simp cong: if_cong)
  oops

thm add_ac
thm mult_ac

lemmas all_ac = add_ac mult_ac
print_theorems

lemma
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<odot>" 70)
  assumes A: "\<And>x y z. (x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  assumes C: "\<And>x y. x \<odot> y = y \<odot> x"
  assumes AC: "\<And>x y z. x \<odot> (y \<odot> z) = y \<odot> (x \<odot> z)"
  shows "(z \<odot> x) \<odot> (y \<odot> v) = v \<odot> (x \<odot> (y\<odot> z))"
  apply (simp only: C)
  apply (simp only: A C)
  apply (simp only: AC)
  done
  
text \<open>when all else fails: tracing the simplifier

typing
  declare [[simp_trace]]        turns tracing on,
  declare [[simp_trace=false]]  turns tracing off
(within a proof, write 'using' rather than 'declare')
\<close>

declare [[simp_trace]]
lemma "A \<and> (A \<longrightarrow> B)"
  apply (simp cong: conj_cong)
  oops
declare [[simp_trace=false]]

\<comment> \<open>single stepping: subst\<close>

thm add.commute
thm add.assoc
declare add.assoc [simp]

lemma "a + b = x + ((y::nat) + z)"
thm add.assoc[symmetric]
  apply (simp add: add.assoc [symmetric] del: add.assoc)
thm add.commute
  apply (subst add.commute [where a=x]) 
  oops


end
