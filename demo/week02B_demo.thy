theory week02B_demo imports Main begin

section{* Propositional logic *}

subsection{* Basic rules *}

text{* \<and> *}
thm conjI 

thm conjunct2
thm conjE 

text{* \<or> *}
thm disjI1 
thm disjI2 
thm disjE

text{* \<longrightarrow> *}
thm impI impE


subsection{* Examples *}

text{* a simple backward step: *}
lemma "A \<and> B" thm conjI
apply(rule conjI)
oops

text{* a simple backward proof: *}
lemma "B \<and> A \<longrightarrow> A \<and> B" 
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done


lemma "(A \<or> B) \<longrightarrow> (B \<or> A)"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done
  

lemma "\<lbrakk> B \<longrightarrow> C; A \<longrightarrow> B \<rbrakk> \<Longrightarrow> A \<longrightarrow> C"
  apply (rule impI)
  apply (erule impE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply assumption
sorry

thm notI notE 

lemma "\<not>A \<or> \<not>B \<Longrightarrow> \<not>(A \<and> B)"
  apply (rule notI)
  apply (erule disjE)
   apply (erule notE)
   apply (erule conjE)
   apply assumption
  apply (erule notE)
  apply (erule conjE)
  apply assumption 
  done

text {* Case distinctions *}

lemma "P \<or> \<not>P"
  apply (case_tac "P")
  oops
  

thm FalseE

lemma "(\<not>P \<longrightarrow> False) \<longrightarrow> P"
oops 


text{* Explicit backtracking: *}

lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
apply(erule conjE)
back
apply(assumption)
done
text {* UGLY! EVIL! AVOID! *}


text{* Implicit backtracking: chaining with , *}

lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
apply (erule conjE, assumption)
done

text{* OR: use rule_tac or erule_tac to instantiate the schematic variables of the rule *}

lemma "\<lbrakk> P \<and> Q; A \<and> B \<rbrakk> \<Longrightarrow> A"
apply (erule_tac P=A and Q=B in conjE)
apply assumption
done

text {* more rules *}
text{* \<and> *}
thm conjunct1 conjunct2

text{* \<or> *}
thm disjCI  

lemma our_own_disjCI: "(\<not>Q \<longrightarrow> P) \<Longrightarrow> P \<or> Q"
(*TODO (with case_tac) *)
  apply (case_tac Q)
   apply (rule disjI2)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

text{* \<longrightarrow> *}
thm mp

text{* = (iff) *}
thm iffI iffE iffD1 iffD2


text{* Equality *}
thm refl sym trans

text{* \<not> *}
thm notI notE

text{* Contradictions *}
thm FalseE ccontr classical excluded_middle

-- {* more rules *}

text {* defer and prefer *}
lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
  prefer 2 
  defer
  sorry

text{* classical propositional logic: *}
lemma Pierce: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption
  apply assumption
  done


text {* Exercises *}


lemma "A \<and> B \<longrightarrow> A \<longrightarrow> B"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)
  apply assumption 
  done

lemma "A \<longrightarrow> (B \<or> C) \<longrightarrow> (\<not> A \<or> \<not> B) \<longrightarrow> C"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule disjE)
   apply (erule disjE)
    apply (erule notE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply assumption
  done

lemma"((A \<longrightarrow> B) \<and> (B \<longrightarrow> A)) = (A = B)"
  apply (rule iffI)
   apply (rule iffI)
    apply (erule conjE)
    apply (erule impE)
     apply assumption
    apply assumption
   apply (erule conjE)
   apply (erule impE)
    apply (erule impE)
     apply assumption
    apply assumption
  apply (erule impE)
    apply assumption 
   apply assumption
  apply (rule conjI)
   apply (rule impI)
  apply (erule iffD1)
   apply assumption
  apply (rule impI)
  apply (erule iffD2)
  apply assumption
  done 

lemma "(A \<longrightarrow> (B \<and> C)) \<longrightarrow> (A \<longrightarrow> C)"
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply assumption 
  apply (erule conjE)
  apply assumption
  done

end
