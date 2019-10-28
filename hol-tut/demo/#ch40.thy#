theory ch40
imports Main
begin

section{* Propositional logic *}


subsection{* Basic rules *}

text{* \<and> *}
thm conjI conjE conjunct1 conjunct2

text{* \<or> *}
thm disjI1 disjI2 disjE

text{* \<longrightarrow> *}
thm impI impE mp

text{* = (iff) *}
thm iffI iffE iffD1 iffD2

text{* \<not> *}
thm notI notE

text{* Contradictions *}
thm FalseE ccontr classical


subsection{* Examples *}

text{* A simple backward step: *}
lemma "A \<and> B"
apply(rule conjI)
oops

text{* A simple backward proof: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)
apply(rule conjE)
 apply(assumption)
apply(rule conjI)
 apply(assumption)
apply(assumption)
done

text{* Elimination rules should be applied with erule: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)
apply(erule conjE)
apply(rule conjI)
 apply(assumption)
apply(assumption)
done

(* For interactive proofs developed together with the students: *)

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
  apply blast+
oops

lemma "\<lbrakk> A \<longrightarrow> B; B \<longrightarrow> C \<rbrakk> \<Longrightarrow> A \<longrightarrow> C"
  apply safe
oops

lemma "\<not>A \<or> \<not>B \<Longrightarrow> \<not>(A \<and> B)"
  apply (erule disjE)
   apply (rule notI)
   apply (erule conjE)
   apply (erule notE)
   apply assumption
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption


subsection{* Further useful techniques *}

text{* Simple proofs are automatic: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(blast)
done

text{* Explicit case distinctions: *}
lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
apply(case_tac P)
 apply(simp)
apply(simp)
done

end
