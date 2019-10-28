theory week03B_demo_HOL imports Pure begin

text \<open>Defining HOL\<close>

text \<open>Technical Setup, introducing a new logic\<close>

class type
default_sort type

typedecl bool 
typedecl ind

axiomatization where bool_arity: "OFCLASS(bool, type_class)"
instance "bool" :: type by (rule bool_arity)

axiomatization where ind_arity: "OFCLASS(ind, type_class)"
instance "ind" :: type by (rule ind_arity)

axiomatization where fun_arity: "OFCLASS('a \<Rightarrow> 'b, type_class)"
instance "fun" :: (type, type) type by (rule fun_arity)

judgment
  Trueprop      :: "bool \<Rightarrow> prop"  ("(_)" 5)

\<comment> \<open>---------------------------------\<close>

axiomatization
  Eq            :: "'a \<Rightarrow> 'a \<Rightarrow> bool"      (infixl "=" 50) and
  Imp           :: "bool \<Rightarrow> bool \<Rightarrow> bool"  (infixr "\<longrightarrow>" 25) and
  Eps           :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"    (binder "SOME" 10)

definition True :: bool
  where "True \<equiv> ((\<lambda>x::bool. x) = (\<lambda>x. x))"

definition All :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "\<forall>" 10)
  where "All P \<equiv> (P = (\<lambda>x. True))"

definition Ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "\<exists>" 10)
  where "Ex P \<equiv> \<forall>Q. (\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> Q"

definition False :: bool
  where "False \<equiv> (\<forall>P. P)"

definition Not :: "bool \<Rightarrow> bool"  ("\<not> _" [40] 40)
  where "\<not> P \<equiv> P \<longrightarrow> False"

definition And :: "[bool, bool] \<Rightarrow> bool"  (infixr "\<and>" 35)
  where "P \<and> Q \<equiv> \<forall>R. (P \<longrightarrow> Q \<longrightarrow> R) \<longrightarrow> R"

definition Or :: "[bool, bool] \<Rightarrow> bool"  (infixr "\<or>" 30)
  where "P \<or> Q \<equiv> \<forall>R. (P \<longrightarrow> R) \<longrightarrow> (Q \<longrightarrow> R) \<longrightarrow> R"

definition If:: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(if (_)/ then (_)/ else (_))" 10)
  where "If P x y \<equiv> SOME z. (P=True \<longrightarrow> z=x) \<and> (P=False \<longrightarrow> z=y)"

definition inj:: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "inj f  \<equiv> \<forall>x y. f x = f y \<longrightarrow> x = y"

definition  surj:: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "surj f \<equiv> \<forall>y. \<exists>x. y = f x"

  
 

text \<open>Additional concrete syntax\<close>

syntax
  "_not_equal"  :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<noteq>" 50)
translations
  "x \<noteq> y"  == "\<not>(x = y)"

text \<open>Axioms and basic definitions\<close>

axiomatization where
  refl:  "t = t"  and
  subst: "\<lbrakk> s = t; P s \<rbrakk> \<Longrightarrow> P t" and
  ext:   "(\<And>x. f x = g x) \<Longrightarrow> (\<lambda>x. f x) = (\<lambda>x. g x)" 

axiomatization where
  impI:  "(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q" and
  mp:    "\<lbrakk> P\<longrightarrow>Q;  (P::bool) \<rbrakk> \<Longrightarrow> Q" and
  iff:   "(P\<longrightarrow>Q) \<longrightarrow> (Q\<longrightarrow>P) \<longrightarrow> (P=Q)" and
  True_or_False: "(P=True) \<or> (P=False)" and
  infinity: "\<exists>f :: ind \<Rightarrow> ind. inj f \<and> \<not>surj f"

axiomatization where
  someI: "P x \<Longrightarrow> P (SOME x. P x)"


text \<open>Deriving the standard proof rules in HOL\<close>


text \<open>Implication\<close>

thm mp

\<comment> \<open>we want to show @{text "\<lbrakk> P \<longrightarrow> Q; P; Q \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"}\<close>
lemma impE:
  assumes PQ: "P \<longrightarrow> Q"
  assumes P: "P"
  assumes QR: "Q \<Longrightarrow> R"
  shows "R"
  apply (rule QR)
  apply (insert PQ) thm mp 
  apply (drule mp)
   apply (rule P)
  apply assumption
  done


\<comment> \<open>-------------------------------\<close>

text \<open>True\<close>

lemma TrueI: "True"
  apply (unfold True_def)
  apply (rule refl)
  done


text \<open>side track: Equality\<close>

lemma sym: "s = t \<Longrightarrow> t = s" thm subst
  apply (erule subst)
  apply (rule refl)
  done

lemma fun_cong: "f = g \<Longrightarrow> f x = g x" thm subst
  apply (erule subst)
  apply (rule refl)
  done

thm mp
thm iff 
lemma iffI:
  assumes PQ: "P \<Longrightarrow> Q"
  assumes QP: "Q \<Longrightarrow> P"
  shows "P = Q" 
  apply (rule mp)
   apply (rule mp)
    apply (insert iff [where P=P and Q=Q])  
    apply assumption
   apply (rule impI)
   apply (rule PQ)
   apply assumption
  apply (rule impI)
  apply (rule QP)
  apply assumption
  done

lemma iffD1: "Q = P \<Longrightarrow> Q \<Longrightarrow> P"
  apply (rule subst)
   apply assumption
  apply assumption
  done

lemma iffD2: "P = Q \<Longrightarrow> Q \<Longrightarrow> P" thm sym
  apply (drule sym)
  apply (erule iffD1)
   apply assumption
  done


text \<open>back to True\<close>

lemma eqTrueI: "P \<Longrightarrow> P = True" 
  apply (rule iffI)
   apply (rule TrueI)
  apply assumption
  done

lemma eqTrueE: "P = True \<Longrightarrow> P" thm iffD2
  apply (drule iffD2)
   apply (rule TrueI)
  apply assumption
  done


\<comment> \<open>-------------------------------\<close>

text \<open>Universal Quantifier\<close>

lemma allI: 
  assumes P: "\<And>x. P x"
  shows "\<forall>x. P x"
  apply (unfold All_def)
  apply (rule ext) thm eqTrueI
  apply (rule eqTrueI)
  apply (rule P)
  done

lemma spec: "\<forall>x. P x \<Longrightarrow> P x"
  apply (unfold All_def) thm eqTrueE
  apply (rule eqTrueE) thm fun_cong
  apply (drule fun_cong)
  apply assumption
  done
 
lemma allE:
  assumes all: "\<forall>x. P x" 
  assumes R: "P x \<Longrightarrow> R" 
  shows "R"
  apply (rule R)
  apply (insert all)
  apply (erule spec)
  done


\<comment> \<open>-------------------------------\<close>

text \<open>False\<close>

lemma FalseE:
  "False \<Longrightarrow> P"
  apply (unfold False_def)
  apply (erule_tac x=P in allE)
  apply assumption
  done

lemma False_neq_True:
  "False = True \<Longrightarrow> P"  thm eqTrueE  
  apply (drule eqTrueE)
  apply (erule FalseE)
  done
  

\<comment> \<open>-------------------------------\<close>

text \<open>Negation\<close>

lemma notI:
  assumes P: "P \<Longrightarrow> False"
  shows "\<not>P"
  apply (unfold Not_def)
  apply (rule impI)
  apply (rule P)
  apply assumption
  done

lemma notE: "\<lbrakk> \<not>P; P \<rbrakk> \<Longrightarrow> R"
  apply (unfold Not_def)
  apply (erule impE)
   apply assumption
  apply (erule FalseE)
  done

lemma False_not_True: "False \<noteq> True"
  apply (rule notI) thm False_neq_True
  apply (erule False_neq_True)
  done


\<comment> \<open>-------------------------------\<close>

text \<open>Existential Quantifier\<close>

lemma exI:
  "P x \<Longrightarrow> \<exists>x. P x"
  apply (unfold Ex_def)
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x=x in allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma exE:
  assumes ex: "\<exists>x. P x"
  assumes R: "\<And>x. P x \<Longrightarrow> R"
  shows "R"
  apply (insert ex)
  apply (unfold Ex_def) thm spec
  apply (drule spec) thm mp
  apply (drule mp)
   apply (rule allI)
   apply (rule impI)
   apply (rule R)
   apply assumption
  apply assumption
  done


\<comment> \<open>-------------------------------\<close>

text \<open>Conjunction\<close>

lemma conjI: "\<lbrakk> P; Q \<rbrakk> \<Longrightarrow> P \<and> Q"
  apply (unfold And_def)
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma conjE:
  assumes PQ: "P \<and> Q"
  assumes R: "\<lbrakk> P; Q \<rbrakk> \<Longrightarrow> R"
  shows R
  apply (insert PQ)
  apply (unfold And_def)
  apply (erule allE)
  apply (erule impE)
   apply (rule impI)
   apply (rule impI)
   apply (rule R)
    apply assumption
   apply assumption
  apply assumption
  done


\<comment> \<open>-------------------------------\<close>

text \<open>Disjunction\<close>

lemma disjI1:
  "P \<Longrightarrow> P \<or> Q"
  apply (unfold Or_def)
  apply (rule allI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma disjI2:
  "Q \<Longrightarrow> P \<or> Q"
  apply (unfold Or_def)
  apply (rule allI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE, assumption, assumption)
  done

lemma disjE:
  assumes PQ: "P \<or> Q"
  assumes P: "P \<Longrightarrow> R"
  assumes Q: "Q \<Longrightarrow> R"
  shows "R"
  apply (insert PQ)
  apply (unfold Or_def)
  apply (erule allE)
  apply (erule impE)
   apply (rule impI)
   apply (rule P)
   apply assumption
  apply (erule impE)
   apply (rule impI)
   apply (rule Q)
   apply assumption
  apply assumption
  done


\<comment> \<open>-------------------------------\<close>

text \<open>Classical Logic\<close>

lemma classical:
  assumes P: "\<not>P \<Longrightarrow> P"
  shows P
  apply (insert True_or_False [where P=P])
  apply (erule disjE)
   apply (erule eqTrueE)
  apply (rule P)
  apply (rule notI)
  apply (rule subst)
   apply assumption
  apply assumption
  done


lemma notnotD:
  "\<not>\<not>P \<Longrightarrow> P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma disjCI:
  assumes P: "\<not>Q \<Longrightarrow> P"
  shows "P \<or> Q"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule P)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma tertium_non_datur: 
  "P \<or> \<not>P"
  apply (rule disjCI)
  apply (drule notnotD)
  apply assumption
  done


\<comment> \<open>-------------------------------\<close>

text \<open>Choice\<close>

lemma someI_ex: "\<exists>x. P x \<Longrightarrow> P (SOME x. P x)" 
  apply (erule exE)
  apply (erule someI)
  done

lemma someI2:
  assumes a: "P a" 
  assumes PQ: "\<And>x. P x \<Longrightarrow> Q x" 
  shows "Q (SOME x. P x)"
  apply (insert a) 
  apply (drule someI, drule PQ)
  apply assumption
  done

lemma some_equality:
  assumes a: "P a"
  assumes P: "\<And>x. P x \<Longrightarrow> x=a"
  shows "(SOME x. P x) = a"
  apply (rule someI2)
   apply (rule a)
  apply (rule P)
  apply assumption
  done

lemma some_eq_ex: 
  "P (SOME x. P x) = (\<exists>x. P x)"
  apply (rule iffI)
   apply (rule exI)
   apply assumption
  apply (erule someI_ex)
  done


\<comment> \<open>-------------------------------\<close>

text \<open>if-then-else\<close>
thm some_equality


lemma if_True:
  "(if True then s else t) = s"
  apply (unfold If_def) 
  apply (rule some_equality)
   apply (rule conjI)
    apply (rule impI)
    apply (rule refl)
   apply (rule impI)
   apply (drule sym)
   apply (erule False_neq_True)
  apply (erule conjE)
  apply (erule impE)
   apply (rule refl)
  apply assumption
  done

lemma if_False:
  "(if False then s else t) = t"
  apply (unfold If_def) thm some_equality
  apply (rule some_equality)
   apply (rule conjI)
    apply (rule impI)
    apply (erule False_neq_True)
   apply (rule impI)
   apply (rule refl)
  apply (erule conjE)
  apply (erule impE, rule refl)
  apply assumption
  done

end
