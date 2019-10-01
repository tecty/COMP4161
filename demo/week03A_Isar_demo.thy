theory week03A_Isar_demo imports Main begin

\<comment> \<open> ------------------------------------------------------------------ \<close>

\<comment> \<open>  {* Motivation *} \<close>

lemma "(A \<longrightarrow> B) = (B \<or> \<not>A)"
by blast

value "True \<longrightarrow> False"
value "False \<or> \<not> True"

lemma "(A \<longrightarrow> B) = (B \<or> \<not>A)"
  (* apply style *)
  apply(rule iffI)
   apply(case_tac A)
    apply(erule (1) impE)
    apply(erule disjI1)
   apply(erule disjI2)
  apply(erule disjE)
   apply(rule impI)
   apply assumption
  apply(rule impI)
  apply(erule notE)
  apply assumption
  done

lemma "(A \<longrightarrow> B) = (B \<or> \<not>A)"
proof (rule iffI)
  assume AB: "A \<longrightarrow> B"
  show "B \<or> \<not> A"
  proof (cases A)
    assume A: "A"
    from AB A have "B" by(rule impE)
    thus ?thesis by(rule disjI1)
  next
    assume "\<not> A"
    thus ?thesis by (rule disjI2)
  qed
next
  assume "B \<or> \<not> A"
  thus "A \<longrightarrow> B"
  proof (rule disjE)
    assume "B"
    thus ?thesis by(rule impI)
  next
    assume notA: "\<not> A"
    show ?thesis
    proof (rule impI)
      assume "A"
      from notA this show "B" by (rule notE)
    qed
  qed
qed

\<comment> \<open> ------------------------------------------------------------------\<close>

\<comment> \<open>  {* Isar *} \<close>

lemma "\<lbrakk> A; B \<rbrakk> \<Longrightarrow> A \<and> B"
proof
  assume A_is_true: "A"
  from A_is_true show "A" by assumption
next
  assume B_is_true: "B"
  from B_is_true show "B" by simp
qed

lemma
  assumes PorQ: "P \<or> Q"
  shows "Q \<or> P"
using PorQ proof
  assume P: "P"
  from P show "Q \<or> P" by(rule disjI2)
next
  assume "Q"
  from this show "Q \<or> P" by(rule disjI1)
qed

lemma
  assumes "A"
  assumes B_is_true: "B"
  shows "A \<and> B"
proof(rule conjI)
  show "B" by (rule B_is_true)
  from `A` show "A" by assumption
qed

lemma "(x::nat) + 1 = 1 + x"
proof -
  have l: "x + 1 = Suc x" by simp
  have r: "1 + x = Suc x" by simp
  show "x + 1 = 1 + x" by (simp only: l r)
qed

\<comment> \<open> ------------------------------------------------------------------\<close>

section "More Isar"

\<comment> \<open>  {* . = by assumption,  .. = by rule *} \<close>

lemma "\<lbrakk> A; B \<rbrakk> \<Longrightarrow> B \<and> A"
proof
  assume "B"
  from `B` show "B"  .
next
  assume "A" from this show "A" .
qed

lemma "\<lbrakk> A; B \<rbrakk> \<Longrightarrow> B \<and> A"
proof -
  assume B: "B" and A: "A"
  from B A show "B \<and> A" by(rule conjI)
qed

\<comment> \<open>  {* backward/forward *} \<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from this have "A" ..
  from `A \<and> B` have "B" ..
  from `B` `A` show "B \<and> A" ..
qed

\<comment> \<open> {* fix *} \<close>

lemma
  assumes P: "\<forall>x. P x"
  shows "\<forall>x. P (f x)"
proof
  fix x
  from P show "P (f x)" by(rule spec)
qed

\<comment> \<open> {* Proof text can only refer to global constants, free variables
in the lemma, and local names introduced via fix or obtain. *} \<close>

lemma
  assumes Pf: "\<exists>x. P (f x)"
  shows "\<exists>y. P y"
proof -
  from Pf show ?thesis
  proof
    fix x
    assume "P (f x)"
    from this show ?thesis ..
  qed
qed

\<comment> \<open>  {* obtain *} \<close>

lemma
  assumes Pf: "\<exists>x. P (f x)"
  shows "\<exists>y. P y"
proof -
  from Pf obtain x where "P (f x)" ..
  from this show ?thesis ..
qed

lemma
  assumes ex: "\<exists>x. \<forall>y. P x y"
  shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  show "\<exists>x. P x y"
  proof -
    from ex obtain x where "\<forall>y. P x y" ..
    hence "P x y" ..
    thus ?thesis ..
  qed
qed


\<comment> \<open>  {* moreover *} \<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from `A \<and> B` have "B" ..
  moreover from `A \<and> B` have "A" ..
  ultimately show "B \<and> A" ..
qed

thm mono_def
thm monoI

lemma
  assumes mono_f: "mono (f::int\<Rightarrow>int)"
      and mono_g: "mono (g::int\<Rightarrow>int)"
  shows "mono (\<lambda>i. f i + g i)"
proof
  fix x y
  assume le: "(x::int) \<le> y"
  from mono_f le have "f x \<le> f y" ..
  moreover from mono_g le have "g x \<le> g y" ..
  ultimately show "f x + g x \<le> f y + g y" by(rule add_mono)
qed

\<comment> \<open> ------------------------------------------------------------------\<close>

\<comment> \<open> {* Isar, case distinction *} \<close>

declare length_tl[simp del]

(* isar style, just using "proof (cases xs)", not using case *)
lemma "length (tl xs) = length xs - 1"
proof(cases xs)
  assume "xs = []" thus ?thesis by simp
next
  fix y ys assume "xs = y#ys" thus ?thesis by simp
qed

(* isar style, using case *)
lemma "length (tl xs) = length xs - 1"
proof(cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  from Cons show ?thesis by simp
qed


\<comment> \<open> {* structural induction *} \<close>

(* apply style *)
lemma "2 * (\<Sum>i<n+1. i) = n*(n+1::nat)"
  apply(induct n, simp_all)
  done

(* isar style, not using case *)
lemma "2 * (\<Sum>i<n+1. i) = n*(n+1::nat)" (is "?P n")
proof(induct n)
  show "?P 0" by simp
next
  fix n
  assume "?P n"
  thus "?P (Suc n)" by simp
qed

(* isar style, using case *)
lemma "2 * (\<Sum>i<n+1. i) = n*(n+1::nat)"
proof(induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from Suc show ?case by simp
qed


lemma
  fixes n::nat
  shows "n < n*n + 1"
proof(induct n)
  case 0 show ?case by simp
next
  case (Suc n) thus ?case by simp
qed

\<comment> \<open> {* induction with @{text"\<And>"} or @{text"\<Longrightarrow>"} *} \<close>

lemma
  assumes A: "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "P (n::nat)"
proof(rule A)
  show "\<And>m. m < n \<Longrightarrow> P m"
  proof(induct n)
    case 0
    thus ?case by simp
  next
    case (Suc n)
    show ?case
    proof(cases)
      assume eq: "m = n"
      from A Suc have "P n" by blast
      with eq show "P m" by simp
    next
      assume neq: "m \<noteq> n"
      from Suc neq have "m < n" by arith
      thus "P m" by(rule Suc)
    qed
  qed
qed

\<comment> \<open> ---------------------------------------------------------------\<close>

end