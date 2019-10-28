theory ch50
imports Main
begin

section{* Predicate logic *}

text{* A warming up exercise: propositional logic. *}
lemma "A \<and> (B \<or> C) \<Longrightarrow> A \<and> B \<or> C"
  apply (erule conjE)
  apply (erule disjE)
   apply (rule  disjI1, rule conjI, assumption+)
  apply (rule disjI2,  assumption+)
  done
subsection{* Quantifier reasoning *}

text{* A successful proof: *}
lemma "\<forall>a. \<exists>b. a = b"
apply(rule allI)
apply(rule_tac x = "a" in exI)
apply(rule refl)
done

text{* Intro and elim resoning: *}
lemma "\<exists>b. \<forall>a. P a b \<Longrightarrow> \<forall>c. \<exists>d. P c d"
(* the safe rules first: *)
apply(rule allI)
apply(erule exE)
(* now the unsafe ones: *)
apply(rule_tac x = "b" in exI)
apply(erule_tac x = "c" in allE)
apply(assumption)
done

text{* Principle:
 First the safe rules (allI, exE: they generate parameters),
 then the unsafe rules (allE, exI: they generate unknowns).
*}

text{* Blast is your friend: *}
lemma "\<exists>b. \<forall>a. P a b \<Longrightarrow> \<forall>c. \<exists>d. P c d"
apply blast
done


subsection{* More Proof methods*}

subsubsection{*More instantiation examples*}

text{* Instantiating allE: *}
lemma "ALL xs. xs@ys = zs \<Longrightarrow> ys=zs"
thm allE
apply(erule_tac x = "[]" in allE)
apply(simp)
done

text{* Instantiating exI: *}
lemma "EX n. P(f n) \<Longrightarrow> EX m. P m"
apply(erule exE)
thm exI
apply(rule_tac x = "f n" in exI)
apply assumption
done


subsubsection{* Forward reasoning *}

lemma "A \<and> B \<Longrightarrow> \<not> \<not> A"
thm conjunct1
apply(drule conjunct1)
apply blast
done

thm dvd_add dvd_refl
thm dvd_add[OF dvd_refl dvd_refl]


subsubsection{* Clarification *}

lemma "\<forall>x y. P x y & Q x y & R x y"
apply(clarify)
oops

lemma "\<forall>x y. x = 5 \<and> y = 7 \<and> y < z \<longrightarrow> P(x+y::nat)"
apply(clarsimp)
oops

end
