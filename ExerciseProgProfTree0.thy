theory ExerciseProgProfTree0
  imports Main
begin

(* No Elem Tree*)
datatype tree0 = Tip | Node tree0 tree0

fun nodes:: "tree0 \<Rightarrow> nat" where 
"nodes Tip = 1" | 
"nodes (Node x y) = 1 + (nodes x) + (nodes y)"

lemma [simp]: "nodes Tip = 1"
  apply auto 
  done 


fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0 " where 
"explode 0 t = t"| 
"explode (Suc n) t = explode n (Node t t)"

lemma nodes_span_rule0 [simp]: " nodes t = n \<Longrightarrow> nodes (Node t t) =  2 * n  + 1"
  apply auto
  done

lemma nodes_plus : "nodes t = n \<Longrightarrow> nodes t + nodes t = 2 * nodes t"
  apply auto 
  done 


lemma [simp]: "nodes (Node t t) = 1 + 2 * (nodes t)"
  apply auto
  done

lemma explode_0 [simp] : "nodes (explode 0 t) = nodes t"
  apply auto
  done 


lemma explode_simp [simp] : "nodes (explode (Suc n) t) = nodes (explode n (Node t t))"
  apply (simp add:nodes_plus)
  done

lemma explode_core_formula : "nodes (explode (Suc i) t) = 1 + 2 * nodes (explode i t)"
  apply auto 

lemma "nodes (explode n t) =  (2^n - 1) + (2 ^ n) * nodes t" 
  apply (simp add:explode_simp)
  sorry 
end
