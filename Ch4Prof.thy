theory Ch4Prof
imports Main
begin

lemma "\<forall> A. \<exists> y. x = y"
  apply auto 
  done

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C" by auto

lemma "\<lbrakk>\<forall> xs \<in> A. \<exists> ys. xs = ys @ ys ; us \<in> A\<rbrakk> \<Longrightarrow> \<exists> n. length us = n + n" by fastforce

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys" 
  using append_eq_append_conv by blast



end