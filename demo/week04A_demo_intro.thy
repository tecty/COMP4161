theory week04A_demo_intro
imports Main
begin
 
lemma div_0: 
  "0 div (x::nat) = 0"
  apply(rule semidom_divide_class.div_0)
  done

thm mult_0

(* All goals up to now have been solvable using intro/elim rules only. Rules
   that are equalities (like those above) can be used as intro rules for
   goals that match their shape. *)
lemma "\<exists> x::nat. x div 2 = 0"
  apply(rule_tac x=0 in exI)
  apply(rule div_0)
  done

(* However, using these rules as intro rules cannot solve the following goal.
   Instead, we need to use these rules to rewrite the left- and right-hand 
   sides of the equality to match each other. *)
lemma "\<exists> x::nat. (x div 2) * 2 = 0 * x"
  apply(rule_tac x=0 in exI)
thm ssubst
thm ssubst[OF div_0]
  apply(rule ssubst[OF div_0])
  apply(rule ssubst[OF mult_0[where n=2]])
  apply(rule ssubst[OF mult_0[where n=0]])
  apply(rule refl)
  done

(* this rewriting is automated by Isabelle's rewrite-engine, called the 
   simplifier. This is what we will be learning about today. *)
lemma "\<exists> x::nat. (x div 2) * 2 = 0 * x"
  apply(rule_tac x=0 in exI)
  apply(simp only: div_0 mult_0)
  done

(* REMINDER: automated tactics (like the simp and blast etc.) work best when
   they don't have to instantiate schematic variables, since automation often
   fails when the automated tactics cannot find the right instantiations. 
   You should instantiate schematic variables in the rules that introduce
   them before applying those rules. *)
lemma "\<exists> x::nat. (x div 2) * 2 = 0 * x"
  apply(rule exI)
  apply(simp only: div_0 mult_0)
  oops

end
