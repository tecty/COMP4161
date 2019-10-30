theory ToyLang_sol
  imports Main
begin

datatype toy_language =
    Skip
    | Seq toy_language toy_language
    | Do toy_language

inductive semantics :: "toy_language \<Rightarrow> toy_language \<Rightarrow> bool" where
  semantics_seq1: "\<lbrakk>semantics p p'\<rbrakk>  \<Longrightarrow> semantics (Seq p q) (Seq p' q)"
| semantics_seq2: "\<lbrakk>p = Skip\<rbrakk>  \<Longrightarrow> semantics (Seq p q) q"
| semantics_do: "semantics (Do P) (Seq p (Do p))"

inductive big_semantics :: "toy_language \<Rightarrow> toy_language \<Rightarrow> bool" where
  big_semantics1: "big_semantics p p"
| big_semantics2: "\<lbrakk>semantics p q; big_semantics q r\<rbrakk> \<Longrightarrow> big_semantics p r"

definition stuck where "stuck p = (\<forall>q. semantics p q \<longrightarrow> False)"

definition terminates where
  "terminates p = (\<exists>q. big_semantics p q \<and> stuck q)"

lemma "terminates Skip"
  unfolding terminates_def stuck_def 
  by(auto simp add: semantics.simps[where ?a1.0="Skip",simplified] intro: big_semantics1)
\<comment> \<open>Step-by-step proof:
  apply(rule exI[where x="Skip"])
  apply(rule conjI)
   apply(rule big_semantics1)
  apply(rule allI)
  apply(subst semantics.simps)
  apply simp
  done
\<close>

thm semantics.simps \<comment> \<open>Loop-prone: contains an instance of itself in the RHS. \<close>

thm semantics.simps[where ?a1.0="Skip"] \<comment> \<open>Specialised to the case where source term is Skip\<close>

thm semantics.simps[where ?a1.0="Skip",simplified] \<comment> \<open>simp normal form of previous lemma\<close>

thm semantics.simps[where ?a1.0="Do p"] \<comment> \<open>Only applies to exactly the blue variable p\<close>

thm semantics.simps[where ?a1.0="Do p" for p] \<comment> \<open>Notice the schematic: applies to any term of the shape "Do _"\<close>

lemmas do_simp = semantics.simps[where ?a1.0="Do p" for p, simplified] \<comment> \<open>lemmas foo = bar saves thm(s) bar under the name foo\<close>

lemmas seq_simp = semantics.simps[where ?a1.0="Seq p q" for p q, simplified]

lemma "terminates Skip"
  unfolding terminates_def stuck_def
  by(auto intro: big_semantics.intros simp add: semantics.simps[where ?a1.0="Skip",simplified])

\<comment> \<open>First try: structural induction on p.\<close>
lemma do_diverges_lemma:
  assumes "big_semantics (Do p) q"
  shows "Ex (semantics q)"
  using assms
  apply(induct p)
  oops
  \<comment> \<open>Goes in circles. Besides, we shouldn't have to care what's in the body; a Do diverges because
      it's a Do, not because of what's in it.\<close>

\<comment> \<open>Second try: rule induction.\<close>
lemma do_diverges_lemma:
  assumes "big_semantics (Do p) q"
  shows "Ex (semantics q)"
  using assms
apply(induct rule: big_semantics.induct)
  nitpick \<comment> \<open>Finds a counterexample that happens to be not spurious.
              The induction ate the information that the original process was a do,
              so our first subgoal is now unprovable.\<close>
  oops

\<comment> \<open>Third try: rule induction, conserving the syntactic information that the first
               argument to big_semantics is "Do p".\<close>
lemma do_diverges_lemma:
  assumes "big_semantics (Do p) q"
  shows "Ex (semantics q)"
  using assms
  apply(induct "Do p" q rule: big_semantics.induct) \<comment> \<open>Tell induct to preserve the structural information about the source term.\<close>
   apply(force simp add: do_simp) \<comment> \<open>First subgoal is now provable!\<close>
   \<comment> \<open>But the second subgoal is unprovable: the induction hypothesis only applies to terms=Do _, but the residual after reducing a Do is a sequential composition\<close>
  apply(erule meta_mp)
  apply(subst (asm) do_simp)
  apply clarify
  apply simp
  oops

\<comment> \<open>Third attempt: Weaken the induction hypothesis.
    Find a weaker syntactic predicate than "equals Do p" that is strong enough so that there will
    always be an outgoing transition, but weak enough so that it's preserved by the transition
    relation (that way we will be able to apply the induction hypothesis).
 \<close>
primrec has_trailing_do where
  "has_trailing_do(Do p) = True"
| "has_trailing_do(Seq p q) = has_trailing_do q" 
| "has_trailing_do(Skip) = False"

lemma not_skip_reduces: "p1 \<noteq> Skip \<Longrightarrow> \<exists>p'. semantics p1 p'"
  apply(induct p1) \<comment> \<open>Structural induction because there's nothing in the assumptions to do rule induction on\<close>
    apply simp
   apply(rename_tac p q)
   apply(case_tac "p \<noteq> Skip"; force intro: semantics.intros) \<comment> \<open>m1; m2 applies m2 to every subgoal produces by m1\<close>
  apply(force intro: semantics.intros) \<comment> \<open>force is like auto except it tries harder, on a single subgoal, and either completely discharges the goal or fails\<close>
  done
  \<comment> \<open>Step-by-step proof:
  apply(induct p1)
    apply simp
   apply clarsimp
   apply(rename_tac p q)
   apply(case_tac "p \<noteq> Skip")
    apply clarsimp
    apply(force intro: semantics.intros)
   apply clarsimp
   apply(force intro: semantics.intros)
  apply(force intro: semantics.intros)
  done\<close>

lemma seq_reduces: "Ex (semantics (Seq p1 p2))"
  by(simp add: not_skip_reduces)

lemma has_trailing_do_reduces:
 "has_trailing_do p \<Longrightarrow> Ex (semantics p)"
  by(induct p; force simp add: do_simp intro: seq_reduces)
 \<comment> \<open> Step-by-step proof
   apply(induct p)
    apply simp
   apply clarsimp
   defer
   apply(rule exI)
   apply(force simp add: do_simp)
  apply(rule seq_reduces)
  done\<close>

lemma has_trailing_do_sem_pres:
  "semantics p q \<Longrightarrow> has_trailing_do p \<Longrightarrow> has_trailing_do q"
proof(induct rule: semantics.induct)
  case (semantics_seq1 p p' q)
  then show ?case by simp
next
  case (semantics_seq2 p q)
  then show ?case by simp
next
  case (semantics_do P p)
  then show ?case by simp
qed

lemma do_diverges_lemma_lemma:
  assumes "big_semantics p q"
  and "has_trailing_do p"
  shows "Ex (semantics q)"
  using assms
  by(induct rule: big_semantics.induct) (auto intro: has_trailing_do_sem_pres has_trailing_do_reduces)

lemma do_diverges_lemma:
  assumes "big_semantics (Do p) q"
  shows "Ex (semantics q)"
  using assms
  by(auto elim: do_diverges_lemma_lemma)
  \<comment> \<open>Step-by-step proof:
  apply(erule_tac do_diverges_lemma_lemma)
  apply simp
  done\<close>

lemma "\<not>terminates(Do p)"
  unfolding terminates_def stuck_def
  by(auto intro: do_diverges_lemma)

end