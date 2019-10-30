theory ToyLang_demo
imports Main
begin 

datatype toy_language = 
  Skip 
  | Seq toy_language toy_language 
  | Do toy_language

inductive semantics :: "toy_language \<Rightarrow> toy_language \<Rightarrow> bool" where 
  semantics_seq1: "\<lbrakk>semantics p p'\<rbrakk> \<Longrightarrow> semantics (Seq p q) (Seq p' q)"
| semantics_seq2: "\<lbrakk>p = Skip \<rbrakk> \<Longrightarrow> semantics (Seq p q) q"
| semantics_do  : "semantics (Do p) (Seq p (Do p))"

inductive big_semantics :: "toy_language \<Rightarrow> toy_language \<Rightarrow> bool" where 
  big_semantics1: "big_semantics p p"
| big_semantics2: "\<lbrakk>big_semantics p q; big_semantics q r\<rbrakk> \<Longrightarrow> big_semantics p r"

definition stuck where 
  "stuck p = (\<forall> q. semantics p q \<longrightarrow> False)"

definition terminates where
  "terminates p = (\<exists>q .big_semantics p q \<and> stuck q)"

thm semantics.simps[where ?a1.0="Skip", simplified] 
lemmas do_simp =  semantics.simps[where ?a1.0="Do p" for p, simplified]

lemma "terminates Skip"
  unfolding terminates_def stuck_def 
  apply (rule exI[where x="Skip"])
  apply (rule conjI)
   apply (rule big_semantics1)
  apply (rule allI)
  apply (subst semantics.simps)
  by simp

primrec has_tailing_do where 
  "has_tailing_do (Do p) = True"
| "has_tailing_do (Seq p q) = has_tailing_do q"
| "has_tailing_do Skip = False"

lemma do_is_fix_point: "big_semantics (Do p) q \<Longrightarrow> q = Do p"
  apply (induct "q")
    apply (simp_all add:big_semantics.intros)
  sorry 


lemma do_will_fix:"semantics p q \<Longrightarrow> has_tailing_do p \<Longrightarrow> has_tailing_do q"
  apply (induct rule:semantics.inducts)
    apply (simp_all add:semantics.intros)
  done 

lemma do_diverge_gen: "p \<noteq> Skip \<Longrightarrow> Ex (semantics p)"
  apply (induct p)
    apply (rule exI)
  by (auto intro:semantics.intros) +

lemma tailing_do_is_not_skip: "has_tailing_do p \<Longrightarrow> p \<noteq> Skip"
  apply (induct p)
    apply (simp_all)
  done

thm do_will_fix[where ?p="Do p", simplified]

lemma big_do_will_fix:
  "big_semantics p q\<Longrightarrow> has_tailing_do p \<Longrightarrow> has_tailing_do q"
  apply (induct rule:big_semantics.induct)
  apply assumption
  by blast 
  
lemma has_tailing_do_diverge:
  "big_semantics p q \<Longrightarrow> has_tailing_do p \<Longrightarrow> Ex (semantics q)"
  apply (frule (1)big_do_will_fix) 
  apply (frule_tac p="q" in tailing_do_is_not_skip)
  by (frule (1)do_diverge_gen)

lemma  do_diverge: "big_semantics (Do p) q \<Longrightarrow> Ex (semantics q)"
  using has_tailing_do_diverge by auto 


lemma "\<not> terminates (Do p)"
  unfolding terminates_def stuck_def 
  apply (clarsimp)
  by (auto intro: do_diverge)

end