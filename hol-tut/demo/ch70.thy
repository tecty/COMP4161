theory Demo1
imports Complex_Main
begin

section{* An introductory example *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume a: "surj f"
  from a have b: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from b have c: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from c show "False" by blast
qed

text{* A bit shorter: *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume a: "surj f"
  from a have b: "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from b show "False" by blast
qed

subsection{* this, then, hence and thus *}

text{* Avoid labels, use this: *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text{* then = from this *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then show "False" by blast
qed

text{* hence = then have, thus = then show *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed


subsection{* Structured statements: fixes, assumes, shows *}

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -  --"no automatic proof step!"
  have "\<exists> a. {x. x \<notin> f x} = f a" using s
    by(auto simp: surj_def)
  thus "False" by blast
qed


section{* Proof patterns *}

subsection{* Propositional logic *}

lemma "P \<longleftrightarrow> Q"
proof
  assume "P"
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

lemma "P \<longrightarrow> Q"
proof
  assume "P"
  show "Q" sorry
qed

lemma "P \<and> Q"
proof
  show "P" sorry
next
  show "Q" sorry
qed

lemma "A = (B::'a set)"
proof
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed

lemma "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

text{* Contradiction *}

(*<*)
lemma P
proof (rule ccontr)
  assume "\<not>P"
  show "False" sorry
qed

text{* Case distinction *}

lemma "R"
proof -
  have "P \<or> Q" sorry
  then show "R"
  proof
    assume "P"
    show "R" sorry
  next
    assume "Q"
    show "R" sorry
  qed
qed


text{* obtain example *}

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed


text{* Interactive exercise: *}

lemma assumes "EX x. ALL y. P x y" shows "ALL y. EX x. P x y"
oops


subsection{* proof with complex method *}

lemma "k dvd (n+k) \<longleftrightarrow> k dvd (n::int)"
proof(auto simp add: dvd_def)
  fix a assume a: "n+k = k*a"
  show "EX b. n = k*b"
  proof
    show "n = k*(a - 1)" using a by(simp add: algebra_simps)
  qed
next
  fix a show "EX b. k*a + k = k*b"
  proof
    show "k*a + k = k*(a+1)" by(simp add: algebra_simps)
  qed
qed


section{* Streamlining proofs *}

subsection{* Pattern matching and ?-variables *}

text{* Show EX *}

lemma fixes x :: real assumes "x < y"
shows "EX z. x < z & z < y" (is "EX z. ?P z")
proof
  show "?P((x+y)/2)" using assms by simp
qed

text{* Multiple EX easier with forward proof: *}

lemma "EX x y :: int. x < z & z < y" (is "EX x y. ?P x y")
proof -
  have "?P (z - 1) (z + 1)" by arith
  thus ?thesis by blast
qed


subsection{* Quoting facts: *}

lemma assumes "x < (0::int)" shows "x*x > 0"
proof -
  from `x<0` show ?thesis by(metis mult_neg_neg)
qed

end
