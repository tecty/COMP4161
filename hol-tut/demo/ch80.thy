theory Demo2
imports Main
begin

section{*Case distinction and induction*}


lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis by simp
qed


subsection{*Structural induction*}


lemma "(\<Sum>i\<le>n. i) = n*(n+1::nat) div 2"
by (induct n, simp_all)


lemma "(\<Sum>i\<le>n. i) = n*(n+1::nat) div 2" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

lemma "(\<Sum>i\<le>n. i) = n*(n+1::nat) div 2"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by simp
qed

text{* If we want to name the variable in the Suc-case: *}

lemma fixes n::nat shows "n < n*n + 1"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc i)
  hence "i+1 < i*i + 2" by simp
  thus ?case by simp
qed

lemma split_list: "x : set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  hence "x = a \<or> x : set xs" by simp
  thus ?case
  proof
    assume "x = a"
    hence "a#xs = [] @ x # xs" by simp
    thus ?thesis by blast
  next
    assume "x : set xs"
    then obtain ys zs where "xs = ys @ x # zs" using Cons by auto
    hence "a#xs = (a#ys) @ x # zs" by simp
    thus ?thesis by blast
  qed
qed


subsection{*Rule induction*}


inductive Ev :: "nat => bool" where
Ev0:  "Ev 0" |
Ev2:  "Ev n \<Longrightarrow> Ev(n+2)"

declare Ev.intros [simp]


lemma "Ev n \<Longrightarrow> \<exists>k. n = 2*k"
proof (induct rule: Ev.induct)
  case Ev0 thus ?case by simp
next
  case Ev2 thus ?case by arith
qed


lemma assumes n: "Ev n" shows "\<exists>k. n = 2*k"
using n proof induct
  case Ev0 thus ?case by simp
next
  case Ev2 thus ?case by arith
qed


lemma assumes n: "Ev n" shows "\<exists>k. n = 2*k"
using n proof induct
  case Ev0 thus ?case by simp
next
  case (Ev2 m)
  then obtain k where "m = 2*k" by blast
  hence "m+2 = 2*(k+1)" by simp
  thus "\<exists>k. m+2 = 2*k" ..
qed


subsection{*Induction with fun*}

fun rot :: "'a list \<Rightarrow> 'a list" where
"rot [] = []" |
"rot [x] = [x]" |
"rot (x#y#zs) = y # rot(x#zs)"


lemma "xs \<noteq> [] \<Longrightarrow> rot xs = tl xs @ [hd xs]"
proof (induct xs rule: rot.induct)
  case 1 thus ?case by simp
next
  case 2 show ?case by simp
next
  case (3 a b cs)
  have "rot (a # b # cs) = b # rot(a # cs)" by simp
  also have "\<dots> = b # tl(a # cs) @ [hd(a # cs)]" by(simp add:3)
  also have "\<dots> = tl (a # b # cs) @ [hd (a # b # cs)]" by simp
  finally show ?case . --" proof by assumption"
qed


lemma "xs \<noteq> [] \<Longrightarrow> rot xs = tl xs @ [hd xs]"
by (induct xs rule: rot.induct, simp_all)


subsection{*Chains of (in)equations*}

text{* A little bit of also/finally inside *}

lemma
fixes m :: int
assumes mn: "abs(m*n) = 1"
shows "abs m = 1"
sorry

(* Fill in the proof! *)


lemma
fixes m :: int
assumes mn: "abs(m*n) = 1"
shows "abs m = 1"
proof -
  have "m \<noteq> 0" "n \<noteq> 0" using mn by auto
  have "\<not> (2 \<le> abs m)"
  proof
    assume "2 \<le> abs m"
    hence "2*abs n \<le> abs m * abs n"
      by(simp add: mult_mono)
    also have "\<dots> = 1" using mn
      by(simp add: abs_mult)
    finally show False using `n \<noteq> 0` by simp
  qed
  thus "abs m = 1" using `m \<noteq> 0` by arith
qed


subsection{* Monotonicity reasoning *}

lemma fixes a :: int shows "(a+b)\<twosuperior> \<le> 2*(a\<twosuperior> + b\<twosuperior>)"
proof -
  have "(a+b)\<twosuperior> \<le> (a+b)\<twosuperior> + (a-b)\<twosuperior>" by simp
  also have "(a+b)\<twosuperior> \<le> a\<twosuperior> + b\<twosuperior> + 2*a*b"
    by(simp add:numeral_2_eq_2 algebra_simps)
  also have "(a-b)\<twosuperior> = a\<twosuperior> + b\<twosuperior> - 2*a*b"
    by(simp add:numeral_2_eq_2 algebra_simps)
  finally show ?thesis by simp
qed


subsection{*Accumulating facts*}


thm mono_def

lemma assumes monof: "mono(f::int\<Rightarrow>int)"
          and monog: "mono(g::int\<Rightarrow>int)"
      shows "mono(\<lambda>i. f i + g i)"
proof --"rule monoI used automatically"
  fix i j :: int
  assume A: "i \<le> j"
  have "f i \<le> f j" using A monof by(simp add:mono_def)
  moreover
  have "g i \<le> g j" using A monog by(simp add:mono_def)
  ultimately show "f i + g i \<le> f j + g j" by arith
qed

lemma dvd_minus:
  assumes du: "(d::int) dvd u"
  assumes dv: "d dvd v"
  shows  "d dvd u - v"
proof -
  from du obtain ku where "u = d * ku" by(fastsimp simp: dvd_def)
  moreover
  from dv obtain kv where "v = d * kv" by(fastsimp simp: dvd_def)
  ultimately have "u - v =  d * ku - d * kv" by simp
  also have "\<dots> = d * (ku - kv)" by (simp add: algebra_simps)
  finally show ?thesis by simp
qed


end
