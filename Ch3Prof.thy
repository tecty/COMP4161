(* Author: z5141448 Toby HUANG *)
theory Ch3Prof
  imports Main
begin
datatype 'a tree =  Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" | 
"set (Node ta a tb) = {a} \<union> set ta \<union> set tb"

fun ord :: "int tree \<Rightarrow> bool " where 
"ord Tip = True" | 
"ord (Node (Node tal va tar) vb (Node tcl vc tcr)) = 
  ((va < vb) \<and> (vb < vc) \<and> ord (Node tal va tar) \<and> ord (Node tcl vc tcr))"  |
"ord (Node Tip vb (Node tcl vc tcr)) = ((vb < vc) \<and> ord (Node tcl vc tcr))" |
"ord (Node (Node tal va tar) vb Tip) = ((va < vb) \<and> ord (Node tal va tar)) " | 
"ord (Node Tip _ Tip ) = True"

fun insert :: "int tree \<Rightarrow> int \<Rightarrow> int tree" where 
"insert Tip a = (Node Tip a Tip)" | 
"insert (Node l v r) a = 
  (if a = v then 
    (Node l v r) 
  else (if a < v then 
    (Node (insert tl a) v r) 
  else 
    (Node l v (insert r a))
  ))
"


end
