theory Check
  imports Submission
begin

theorem while_free_fuel: "while_free c \<Longrightarrow> \<exists>f s' f'. exec c s f = (s', f') \<and> f' > 0"
  by (rule Submission.while_free_fuel)

theorem bigstep_imp_exec: "(c,s) \<Rightarrow> s' \<Longrightarrow> \<exists>f f'. f' > 0 \<and> exec c s f = (s', f')"
  by (rule Submission.bigstep_imp_exec)

lemma exec_fuel_nonincreasing:
  "exec c s f = (s', f') \<Longrightarrow> f' \<le> f"
  by (rule Submission.exec_fuel_nonincreasing)

lemma exec_add: "exec c s f = (s', f') \<Longrightarrow> f' > 0 \<Longrightarrow> exec c s (f + k) = (s', f' + k)"
  by (rule Submission.exec_add)

theorem exec_imp_bigstep: "exec c s f = (s', f') \<Longrightarrow> f' > 0 \<Longrightarrow> (c,s) \<Rightarrow> s'"
  by (rule Submission.exec_imp_bigstep)

end