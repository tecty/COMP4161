theory ch32
imports Main
begin

(* HINT FOR ONLINE DEMO
   Start your first proof attempt with
   itrev xs [] = rev xs
   then generalize by introducing ys, and finally quantify over ys.
   Each generalization should be motivated by the previous failed
   proof attempt.
   This example can also be found in the Isabelle/HOL tutorial.
*)

primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
apply(induct xs arbitrary: ys)
apply(auto)
done

end
