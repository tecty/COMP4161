theory ch62
imports Main 
begin

section{* blast *}

text{*
 Most simple proofs in FOL and set theory are automatic.
 Example: if T is total, A is antisymmetric
 and T is a subset of A, then A is a subset of T.
*}

lemma AT:
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast

text{* The proof: *}
prf AT

lemma "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
by blast


text{* Beyond blast (for pure logic): metis *}

lemma "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
by metis

lemma "(\<forall>x. \<exists>y. P x y) \<longleftrightarrow> (\<exists>f. \<forall>x. P x (f x))"
by metis

lemma "lives agatha \<and> lives butler \<and> lives charles \<and>
       (killed agatha agatha \<or> killed butler agatha \<or> killed charles agatha) \<and>
       (\<forall>x y. killed x y \<longrightarrow> hates x y \<and> \<not> richer x y) \<and>
       (\<forall>x. hates agatha x \<longrightarrow> \<not> hates charles x) \<and>
       hates agatha agatha \<and> hates agatha charles \<and>
       (\<forall>x. lives x \<and> \<not> richer x agatha \<longrightarrow> hates butler x) \<and>
       (\<forall>x. hates agatha x \<longrightarrow> hates butler x) \<and>
       (\<forall>x. \<not> hates x agatha \<or> \<not> hates x butler \<and> \<not> hates x charles) \<longrightarrow>
       (\<exists>x. killed x agatha)"
by metis


text{* Beyond pure logic: *}

lemma "R^* \<subseteq> (R \<union> S)^*"
oops


section{* Sledgehammer!!! *}

lemma "(i::int) div k = 0  \<longleftrightarrow>  k=0 | 0<=i & i<k | i<=0 & k<i"
 using zdiv_eq_0_iff by blast



section{* Arithmetic *}

lemma "\<forall> (k::nat) > 7. \<exists> i j. k = 3*i + 5*j"
by arith

text{* \<rightarrow> Frobenius number *}

lemma "(x::nat)^2 + y^2 + z^2 = 1 \<Longrightarrow> (x + y + z)^2 \<le> 3"
  sledgehammer
  by (metis (no_types, lifting) One_nat_def Suc_leI add.left_neutral add_cancel_left_right add_right_cancel le_neq_trans le_numeral_extra(4) less_imp_le neq0_conv not_add_less2 numeral_le_one_iff semiring_norm(70) zero_eq_power2)

end