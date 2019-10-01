(* A simple comment *)

theory week01A_demo imports Main
begin

text \<open>This is also a comment but it generates nice \LaTeX-text!\<close>

text \<open>
 Note that free variables (eg @{term x}), 
 bound variables (eg @{term "\<lambda>n. n"}) and
 constants (eg @{term Suc}) are displayed differently.
\<close>

term "x"
term "Suc x" 
term "Succ x"
term "Suc x = Succ y"
term "\<lambda>x. x"

text \<open>To display more types inside terms:\<close>
declare [[show_types]]
term "Suc x = Succ y"

text \<open>To switch off again:\<close>
declare [[show_types=false]]
term "Suc x = Succ y"


text \<open>0 and + are overloaded:\<close>

prop "n + n = 0"
prop "(n::nat) + n = 0"
prop "(n::int) + n = 0"
prop "n + n = Suc m"

text\<open>A bound variable:\<close>
term "\<lambda>x. x v"
term "\<lambda>x. Suc x < y"
prop "map (\<lambda>n. Suc n + 1) [0, 1] = [2, 3]"


text \<open>Terms must be type correct!\<close>
term "Suc n = True"


text \<open>Displaying theorems, schematic variables\<close>

thm conjI
text \<open>Schematic variables have question marks and can be instantiated:\<close>
thm conjI [where ?Q = "x"]
thm impI
thm disjE


text \<open>
  You can use \texttt{term}, \texttt{prop} and \texttt{thm} in \LaTeX
  sections, too!  The lemma conjI is: @{thm conjI}. Nicer version, 
  without schematic variables: @{thm conjI [no_vars]}.
\<close>

thm conjI [no_vars]

text \<open>Finding theorems\<close>

text \<open>Searching for constants/functions:\<close>
find_theorems "map"

text \<open>A list of search criteria finds thms that match all of them:\<close>
find_theorems "map" "zip"

text \<open>To search for patterns, use underscore:\<close>
find_theorems "_ + _ = _ - _"
find_theorems "_ + _" "_ < _" "Suc"

text \<open>Searching for theorem names:\<close>
find_theorems name: "conj"

text \<open>They can all be combined, theorem names include the theory name:\<close>
find_theorems "_ \<and> _" name: "HOL." -name: "conj"

text \<open>Stating theorems and a first proof\<close>

lemma "A \<longrightarrow> A"
  \<comment> \<open>a single line comment\<close>
  \<comment> \<open>note the goals window\<close> 
  apply (rule impI)  
  apply assumption
  done

text \<open>
  A proof is a list of {\tt apply} statements, terminated by {\tt done}.

  {\tt apply} takes a proof method as argument (assumption, rule,
  etc.). It needs parentheses when the method consists of more than
  one word.  
\<close>


text \<open>Isabelle doesn't care if you call it lemma, theorem or corollary\<close>

theorem "A \<longrightarrow> A" 
  apply (rule impI)
  apply assumption
  done

corollary "A \<longrightarrow> A" 
  apply (rule impI)
  apply assumption
  done
  
text \<open>You can give it a name, too\<close>

lemma mylemma: "A \<longrightarrow> A" by (rule impI)


text \<open>Abandoning a proof\<close>

lemma "P = NP"
  \<comment> \<open>this is too hard\<close>
  oops

text \<open>Isabelle forgets the lemma and you cannot use it later\<close>

text \<open>Faking a proof\<close>

lemma "P \<noteq> NP"
  \<comment> \<open>have an idea, will show this later\<close>
  sorry

text \<open>
  {\tt sorry} only works interactively (and in {\em quick-and-dirty-mode}), 
  and Isabelle keeps track of what you have faked.
\<close>


text \<open>Proof styles\<close>

\<comment> \<open>automatic\<close>
theorem Cantor: "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)" by best

\<comment> \<open>exploring, but unstructured\<close>
theorem Cantor': "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)" 
  apply (rule_tac x = "{x. x \<notin> f x}" in exI)
  apply (rule notI) 
  apply clarsimp
  apply blast
  done    

\<comment> \<open>structured, explaining\<close>
theorem Cantor'': "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume yin: "y \<in> ?S"
      hence "y \<notin> f y" by simp
      hence "y \<notin> ?S"  by(simp add:fy)
      thus False using yin by contradiction
    next
      assume yout: "y \<notin> ?S"
      hence "y \<in> f y" by simp
      hence "y \<in> ?S"  by(simp add:fy)
      thus False using yout by contradiction
    qed
  qed
qed

find_theorems "Suc (Suc _)"
find_theorems "(_ + _) + _ = _ + (_ + _)"

end
