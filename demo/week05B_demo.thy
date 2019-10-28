theory week05B_demo
imports Main
begin

inductive Ev :: "nat \<Rightarrow> bool"
where
ZeroI: "Ev 0" |
Add2I: "Ev n \<Longrightarrow> Ev (Suc(Suc n))"

print_theorems


\<comment> \<open>---------------------------------------------------\<close>

section "Formalising Least Fixpoints"


definition
  closed :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "closed f B \<equiv> f B \<subseteq> B"

lemma closed_int:
  "\<lbrakk> mono f; closed f A; closed f B \<rbrakk> \<Longrightarrow> closed f (A \<inter> B)"
  thm mono_def 
  apply (unfold closed_def mono_def) 
  apply blast
  done

definition
  lfpt :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "lfpt f \<equiv> \<Inter> {B. closed f B}"


text \<open>lfpt is the greatest lower bound:\<close>

lemma lfpt_lower: "closed f B \<Longrightarrow> lfpt f \<subseteq> B"
  sorry


lemma lfpt_greatest:
  assumes A_smaller: "\<And>B. closed f B \<Longrightarrow> A \<subseteq> B"
  shows "A \<subseteq> lfpt f"
  sorry


section \<open>Fix Point\<close>
  

lemma lfpt_fixpoint1:
  "mono f \<Longrightarrow> f (lfpt f) \<subseteq> lfpt f"
  sorry

  
lemma lfpt_fixpoint2:
  "mono f \<Longrightarrow> lfpt f \<subseteq> f(lfpt f)"
  sorry

lemma lfpt_fixpoint:
  "mono f \<Longrightarrow> f (lfpt f) = lfpt f"
  apply (rule equalityI)
   apply (erule lfpt_fixpoint1)
  apply (erule lfpt_fixpoint2)
  done

text \<open>lfpt is the least fix point\<close>

lemma lfpt_least:
  assumes A: "f A = A"
  shows "lfpt f \<subseteq> A"
  sorry


section \<open>Rule Induction\<close>

consts R :: "('a set \<times> 'a) set"

definition
  R_hat :: "'a set \<Rightarrow> 'a set" where
  "R_hat A \<equiv> undefined"

lemma sound:
  assumes hyp: "\<forall>(H,x) \<in> R. (\<forall>h \<in> H. P h) \<longrightarrow> P x" 
  shows "\<forall>x \<in> lfpt R_hat. P x"
  sorry

end
