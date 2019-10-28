theory ch31
imports Main
begin

section{* How to simplify *}

text{* No assumption: *}
lemma "ys @ [] = []"
apply(simp)
oops (* abandon proof *)

text{* Simple assumption: *}
lemma "xs = [] ==> xs @ ys = ys @ xs @ ys"
apply(simp)
oops;

text{* Simplification in assumption: *}
lemma "[| xs @ zs = ys @ xs; [] @ xs = [] @ [] |] ==> ys = zs"
apply(simp)
done;

text{* Using additional rules: *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply(simp add: ring_distribs) thm ring_distribs
done

text{* Giving a lemma the simp-attribute: *}
declare ring_distribs [simp]


subsection{* Rewriting with definitions *}

definition exor :: "bool => bool => bool" where
"exor x y = (x & y | ~x & ~y)"
definition nand :: "bool => bool => bool" where
"nand x y = (~(x & y))"

text{* Unfolding + simplification: *}
lemma "exor x x = nand x (~x)"
apply(unfold exor_def nand_def)
apply(simp)
done

text{* Just simplification: *}
lemma "exor x x = nand x (~x)"
apply(simp add: exor_def nand_def)
done

subsection{* Case distinctions *}

text{* Automatic: *}
lemma "(A & B) = (if A then B else False)"
apply(simp)
done

lemma "if A then B else C"
apply(simp)
oops

text{* By hand (for case): *}
lemma "x = (case x of 0 => n | Suc y => y+y)"
apply(simp split: nat.split)
oops;

subsection {* Arithmetic *}

text{* A bit of linear arithmetic (no multiplication) is automatic: *}
lemma "[| (x::nat) <= y+z; z+x < y |] ==> x < y"
apply(simp)
done


subsection{* Tracing: *}

lemma "rev[x] = []"
apply(simp)
oops

subsection{* Auto *}

text{* Method ``auto'' can be modified almost like ``simp'': instead of
``add'' use ``simp add'': *}

lemma "(EX u::nat. x=y+u) --> a*(b+c)+y <= x + a*b+a*c"
apply(auto simp add: add_mult_distrib2)
done

end
