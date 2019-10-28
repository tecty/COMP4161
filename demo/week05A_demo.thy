theory week05A_demo
imports Main
begin

\<comment> \<open>---------------------------------------------------\<close>

text\<open>A manual proof in set theory:\<close>

thm equalityI subsetI UnI1 UnI2 UnE

lemma "(A \<union> B) = (B \<union> A)" 
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule UnE)
    apply (erule UnI2)
   apply (erule UnI1)
  apply (rule subsetI)
  apply (erule UnE)
  apply (rule  UnI2, assumption)
  apply (rule  UnI1, assumption)
  done


thm subsetD
declare [[simp_trace = false]]
lemma "(A\<union>B \<subseteq> C) = (A\<subseteq>C \<and> B\<subseteq>C)"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule subsetI)
    apply (erule subsetD)
    apply (rule UnI1)
    apply (assumption)
   apply (rule subsetI)
   apply (erule subsetD)
   apply (rule UnI2)
   apply assumption
  apply (erule conjE)
  apply (rule subsetI)
  apply (erule UnE)
   apply (erule subsetD, assumption)
  apply (erule subsetD, assumption)
  done 
lemma "{a,b} \<inter> {b,c} = (if a \<noteq> c then {b} else {a,b})"
  apply simp
  apply blast
  done

text\<open>Most simple proofs in set theory are automatic:\<close>

lemma "-(A \<union> B) = (-A \<inter> -B)"
  by blast

lemma "{x. P x \<and> Q x} = {x. P x} \<inter> {x. Q x}"
  by blast


\<comment> \<open>--------------------------------------------\<close>

text \<open>Introducing new types\<close>

\<comment> \<open>a new "undefined" type:\<close>
typedecl names 
consts blah :: names


\<comment> \<open>simple abbreviation:\<close>
type_synonym 'a myrel = "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition
  eq :: "'a myrel"
where
  "eq x y \<equiv> (x = y)"
term "eq"

\<comment> \<open>type definition: pairs\<close>

typedef three = "{0::nat,1,2}"
 apply (rule_tac x=1 in exI)
 apply blast
 done

print_theorems

definition prd :: "('a \<Rightarrow> 'b \<Rightarrow> bool) set" where
  "prd \<equiv> {f. \<exists>a b. f = (\<lambda>x y. x=a \<and> y=b)}"

typedef  
  ('a, 'b) prd = "prd::('a \<Rightarrow> 'b \<Rightarrow> bool) set"
  by (auto simp: prd_def)
  (* To understand this proof, try:
  apply (simp add: prd_def)
  -- "just need to exhibit *one* pair, any"
  apply (rule_tac x="\<lambda>x y. x=blah1 \<and> y=blah2" in exI)
  apply (rule_tac x=blah1 in exI)
  apply (rule_tac x=blah2 in exI)
  apply (rule refl)
  done
  *)
  
print_theorems 

definition
  pair :: "'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) prd"
where
  "pair a b \<equiv> Abs_prd (\<lambda>x y. x = a \<and> y = b)"

definition
  fs :: "('a,'b) prd \<Rightarrow> 'a"
where
  "fs x \<equiv> SOME a. \<exists>b. x = pair a b"

definition
  sn :: "('a,'b) prd \<Rightarrow> 'b"
where
  "sn x \<equiv> SOME b. \<exists>a. x = pair a b"

lemma in_prd: "(\<lambda>x y. x = c \<and> y = d) \<in> prd"
  apply (unfold prd_def)
  apply blast
  done

thm iffD1
thm Abs_prd_inject
thm in_prd
thm fun_cong
lemma pair_inject:
  "pair a b = pair a' b' \<Longrightarrow> a=a' \<and> b=b'"
  (*TODO*)
  apply (unfold pair_def)
  apply (insert in_prd [of a b])
  apply (insert in_prd [of a' b'])
  apply (blast dest:Abs_prd_inject fun_cong)
  done

thm pair_inject
lemma pair_eq:
  "(pair a b = pair a' b') = (a=a' \<and> b=b')"
  by (blast dest: pair_inject)

lemma fs:
  "fs (pair a b) = a"
  apply (unfold fs_def)
  apply (blast dest: pair_inject)
  done

lemma sn:
  "sn (pair a b) = b"
  apply (unfold sn_def)
  apply (blast dest: pair_inject)
  done


\<comment> \<open>--------------------------------------------\<close>

section\<open>Inductive definitions\<close>

subsection\<open>Inductive definition of finite sets\<close>

inductive_set Fin :: "'a set set"
where
emptyI:  "{} \<in> Fin" |
insertI: "A \<in> Fin \<Longrightarrow> insert a A \<in> Fin"

print_theorems

subsection\<open>Inductive definition of the even numbers\<close>

inductive_set Ev :: "nat set"
where
ZeroI: "0 \<in> Ev" |
Add2I: "n \<in> Ev \<Longrightarrow> Suc(Suc n) \<in> Ev"

print_theorems


text\<open>Using the introduction rules:\<close>
lemma "Suc(Suc(Suc(Suc 0))) \<in> Ev"
  apply (rule Add2I)
  apply (rule Add2I)
  apply (rule ZeroI)
  done

text\<open>Using the case elimination rules:\<close>
lemma "n \<in> Ev \<Longrightarrow> n = 0 \<or> (\<exists>n' \<in> Ev. n = Suc (Suc n'))"
  thm Ev.cases
  apply(blast elim: Ev.cases)
  done

text\<open>A simple inductive proof:\<close>
lemma "n \<in> Ev \<Longrightarrow> n+n \<in> Ev"
  thm Ev.induct
  apply (erule Ev.induct)
   apply simp
   apply (rule ZeroI)
  apply simp
  apply (rule Add2I)+
  apply assumption
  done 


text\<open>You can also use the rules for Ev as conditional simplification
rules. This can shorten proofs considerably.  \emph{Warning}:
conditional rules can lead to nontermination of the simplifier.  The
rules for Ev are OK because the premises are always `smaller' than the
conclusion. The list of rules for Ev is contained in Ev.intros.\<close>
thm Ev.intros
declare Ev.intros[simp]

text\<open>A shorter proof:\<close>

lemma "n \<in> Ev \<Longrightarrow> n+n \<in> Ev"
  apply(erule Ev.induct)
  apply(simp_all)
  done

text\<open>Nice example, but overkill: don't need assumption 
@{prop "n \<in>Ev"} because @{prop"n+n \<in> Ev"} is true for all @{text n}.

However, here we really need the assumptions:\<close>

lemma "\<lbrakk> m \<in> Ev; n \<in> Ev \<rbrakk> \<Longrightarrow> m+n \<in> Ev"
  apply(erule Ev.induct)
  apply(auto)
  done

text\<open>An inductive proof of @{prop "1 \<notin> Ev"}:\<close>
thm Ev.induct
lemma "n \<in> Ev \<Longrightarrow> n \<noteq> 1"
  apply(erule Ev.induct)
  apply(simp)+ 
  done

text\<open>The general case:\<close>
lemma "n \<in> Ev \<Longrightarrow> \<not>(\<exists>k. n = 2*k+1)"
  apply(erule Ev.induct)
   apply simp
  apply arith
  done


subsection\<open>Proofs about finite sets\<close>

text\<open>Above we declared @{text Ev.intros} as simplification rules.
Now we declare @{text Fin.intros} as introduction rules (via attribute
``intro''). Then fast and blast use them automatically.\<close>

declare Fin.intros [intro]
thm Fin.intros
thm Fin.induct
lemma "\<lbrakk> A \<in> Fin; B \<in> Fin \<rbrakk> \<Longrightarrow> A \<union> B \<in> Fin"
  apply(erule Fin.induct)
   apply simp
  apply auto
  done

lemma "\<lbrakk> A \<in> Fin; B \<subseteq> A \<rbrakk> \<Longrightarrow> B \<in> Fin"
  apply(erule Fin.induct)
txt\<open>The base case looks funny: why is the premise not @{prop "B \<subseteq> {}"}?
Because @{prop "B \<subseteq> A"} was not part of the conclusion we prove.
Relief: pull @{prop "B \<subseteq> A"} into the conclusion with the help of @{text"\<longrightarrow>"}.
\<close>
oops

lemma "A \<in> Fin \<Longrightarrow> B \<subseteq> A \<longrightarrow> B \<in> Fin"
apply(erule Fin.induct)
 apply auto[1]
apply (clarsimp del: subsetI)
txt\<open>We need to strengthen the theorem: quantify @{text B}.\<close>
oops

lemma "A \<in> Fin \<Longrightarrow> \<forall>B. B \<subseteq> A \<longrightarrow> B \<in> Fin"
apply(erule Fin.induct)
 apply(simp)
 apply(rule Fin.emptyI)
apply(rule allI)
apply(rule impI)
apply simp thm subset_insert_iff insert_Diff
apply (simp add:subset_insert_iff)
apply(simp add:subset_insert_iff split:if_split_asm)
apply(drule_tac A = B in insert_Diff)
apply(erule subst)
apply(blast)
done

\<comment> \<open>---------------------------------------------------\<close>

section "Inductive Predicates"

text \<open>The whole thing also works for predicates directly:\<close>

inductive 
  even :: "nat \<Rightarrow> bool"
where
  0: "even 0" |
  2: "even n \<Longrightarrow> even (Suc (Suc n))"

print_theorems

end
