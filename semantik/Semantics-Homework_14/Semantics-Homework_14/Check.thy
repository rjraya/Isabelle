theory Check
  imports Submission
begin

context
  fixes f :: "'a set \<Rightarrow> 'a set" and x\<^sub>0 :: "'a set"
  assumes "mono f" and post_fixpoint: "x\<^sub>0 \<subseteq> f x\<^sub>0"
begin

theorem postfix_step: "\<Union> {(f^^i)(x\<^sub>0) | i :: nat. True} \<subseteq> \<Union> {(f^^(Suc i))(x\<^sub>0) | i :: nat. True}"
  using \<open>mono f\<close> post_fixpoint by (rule Submission.postfix_step)

end

context
  fixes f :: "'a set \<Rightarrow> 'a set"
  assumes continuous: "\<And>X. X\<noteq>{} \<Longrightarrow> f (\<Union>X) = \<Union>(f ` X)"
begin

theorem mono: "x \<subseteq> y \<Longrightarrow> f x \<subseteq> f y"
  using continuous by (rule Submission.mono)

theorem lfp_ge: "\<Union>{(f^^i) {} | i. True} \<subseteq> lfp f"
  using continuous by (rule Submission.lfp_ge)

theorem lfp_le: "lfp f \<subseteq> \<Union>{(f^^i) {} | i. True}" (is "_ \<subseteq> \<Union>?S")
  using continuous by (rule Submission.lfp_le)

end

end