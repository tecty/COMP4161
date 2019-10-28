theory Demo
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

lemma "Tip ~= Node l x r"
apply auto
done

lemma "(1::nat) \<le> (case t of Tip \<Rightarrow> 1 | Node l x r \<Rightarrow> x+1)"
apply(case_tac t)
apply auto
done

primrec  mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

lemma [simp]: "mirror(mirror t) = t"
apply(induct t)
apply auto
done

(* fun *)

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"
apply(induct a xs rule: sep.induct)
apply auto
done

end
