theory week03B_demo_automation imports Main begin

definition 
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"


  
  
  
  
  
  
  
  
  
  
  
  
  

lemma xorI [intro!]:
  "\<lbrakk> \<lbrakk>A; B\<rbrakk> \<Longrightarrow> False; \<not>B \<Longrightarrow> A \<rbrakk> \<Longrightarrow> xor A B"
  apply (unfold xor_def)
  apply blast
  done

lemma xorE:
  "\<lbrakk> xor A B; \<lbrakk>A; \<not>B\<rbrakk> \<Longrightarrow> R; \<lbrakk>\<not>A; B\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply (unfold xor_def)
  apply blast
  done

lemma "xor A A = False" by (blast elim!: xorE)

declare xorE [elim!]

lemma "xor A B = xor B A" by blast

end