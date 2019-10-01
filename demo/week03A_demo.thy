theory week03A_demo imports Main begin

\<comment> \<open> ------------------------------------ \<close>

\<comment> \<open>  {* Quantifier reasoning *} \<close>

\<comment> \<open> {* A successful proof: *} \<close>
lemma "\<forall>a. \<exists>b. a = b"
  apply (rule allI) thm exI
  apply (rule_tac x=a in exI)
  apply (rule refl)
  done

\<comment> \<open> {* An unsuccessful proof: *} \<close>
lemma "\<exists>y. \<forall>x. x = y"
apply(rule exI)
apply(rule allI) thm refl
apply(rule refl)
oops

\<comment> \<open> {* Intro and elim reasoning: *} \<close>
lemma "\<exists>b. \<forall>a. P a b \<Longrightarrow> \<forall>a. \<exists>b. P a b"
  apply (rule allI)
  apply (erule exE)thm exI
  apply (rule_tac x=b in exI)
  apply (erule_tac x=a in allE)
  apply assumption
  done
 (* the safe rules first! *)
 (* (check what happens if you use unsafe rule too early) *)


\<comment> \<open>  {* Instantiation in more detail: *} \<close>

\<comment> \<open> {* Instantiating allE: *} \<close>
lemma "\<forall>x. P x \<Longrightarrow> P 37"
  thm allE
  apply (erule_tac x="37" in allE)
  apply assumption
  done

\<comment> \<open> {* Instantiating exI: *} \<close>

lemma "\<exists>n. P (f n) \<Longrightarrow> \<exists>m. P m"
  apply (erule exE)
  apply (rule_tac x="f n" in exI)
  apply assumption
  done


\<comment> \<open> {* Instantiation removes ambiguity: *} \<close>
lemma "\<lbrakk> A \<and> B; C \<and> D \<rbrakk> \<Longrightarrow> D"
apply(erule_tac P = "C" and Q="D" in conjE)
(* without instantiation, the wrong one is chosen (first) *)
apply assumption
done


\<comment> \<open>  {* Instantiation with "where" and "of" *} \<close>

thm conjI
thm conjI [of "A" "B"]
thm conjI [where Q = "f x"]

\<comment> \<open>  ---------------------------------------------- \<close>

\<comment> \<open> {* Renaming parameters: *} \<close>

lemma "\<And>x y z. P x y z"
apply(rename_tac a b)
oops

lemma "\<forall>x. P x \<Longrightarrow> \<forall>x. \<forall>x. P x"
apply(rule allI)
apply(rule allI)
apply(rename_tac y)
apply(erule_tac x=y in allE)
apply assumption
done




\<comment> \<open>  {* Forward reasoning: drule/frule/OF/THEN*} \<close>

lemma "A \<and> B \<Longrightarrow> \<not> \<not> A"
thm conjunct1
apply (drule conjunct1) thm notI
apply (rule notI) thm notE
apply (erule notE)
apply assumption
done


lemma "\<forall>x. P x \<Longrightarrow> P t \<and> P t'"

  
  apply (frule_tac x="t" in spec)
  apply (drule_tac x="t'" in spec)
  apply (rule conjI)
   apply assumption
  apply assumption
  done


thm dvd_add dvd_refl
thm dvd_add [OF dvd_refl]
thm dvd_add [OF dvd_refl dvd_refl]


\<comment> \<open>  --------------------------------------------- \<close>

\<comment> \<open>  {* Epsilon *} \<close>

lemma "(\<exists>x. P x) = P (SOME x. P x)"
  apply (rule iffI)
  apply (erule exE)
   apply (rule_tac x="x" in someI)  
   apply assumption
  apply (rule_tac x="(SOME x. P x)" in exI)
  apply assumption
  done


\<comment> \<open>  {* Automation *} \<close>

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
apply (intro allI conjI)
oops

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
apply clarify
oops

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
apply safe
oops

lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply blast
done

lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply fast
done


\<comment> \<open>  --------------------------------------------- \<close>

\<comment> \<open>  {* Exercises *} \<close>

\<comment> \<open>  "Quantifier scope is important:" \<close>
lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)" 
  apply(rule iffI)
   apply(rule impI) 
   apply(erule exE)
   apply (erule_tac x=x in allE)
   apply (erule mp)
   apply assumption
  apply(rule allI)
  apply (rule impI)
  apply (erule impE)
   apply (rule_tac x=x in exI)
   apply assumption
  apply assumption
  done
  

\<comment> \<open> {*
   Derive the axiom of choice from the SOME operator (using the rule someI), i.e.
   using only the rules: allI, allE, exI, exE and someI; with only the
   proof methods: rule, erule, rule_tac, erule_tac and assumption, prove:
*} \<close>
 thm someI
 
lemma choice:
  "\<forall>x. \<exists>y. R x y \<Longrightarrow> \<exists>f. \<forall>x. R x (f x)" 
  apply(rule exI)
  apply(rule allI)
  apply(erule allE)
  apply(erule exE)

oops

end
