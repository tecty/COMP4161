theory week04A_demo_simp imports Main begin

text \<open>Simplification\<close>


text \<open>
Lists: 
  @{term "[]"}       empty list
  @{term "x#xs"}     cons (list with head x and tail xs)
  @{term "xs @ ys"}  append xs and ys
\<close>

lemma "ys @ [] = []"
apply(simp)
oops 

definition
  a :: "nat list"
where
  "a \<equiv> []"

definition
  b :: "nat list"
where
  "b \<equiv> []"

text \<open>simp add, rewriting with definitions\<close>
lemma "xs @ a = xs" 
  apply (simp add: a_def)
  done

text \<open>simp only\<close>
lemma "xs @ a = xs"
  apply (simp only: a_def)
  apply simp
  done


lemma ab [simp]: "a = b" by (simp add: a_def b_def)
lemma ba [simp]: "b = a" by simp

text \<open>simp del, termination\<close>
lemma "a = []"
  
  (*apply (simp add: a_def)  
   does not terminate *)
  apply (simp add: a_def del: ab) 
  done


text\<open>Simple assumption:\<close>
lemma "xs = [] \<Longrightarrow> xs @ ys = ys @ xs @ ys"
  apply simp
  oops

text\<open>Simplification in assumption:\<close>
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
  apply simp
  done


end
