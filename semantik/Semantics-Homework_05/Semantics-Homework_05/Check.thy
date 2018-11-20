theory Check
  imports Submission
begin

theorem eq_step: "(c,s) \<rightarrow> (c',s') \<longleftrightarrow> (\<exists>e. cfg c e c' \<and> e s = Some s')"
  by (rule Submission.eq_step)

theorem eq_path: "(c,s) \<rightarrow>* (c',s') \<longleftrightarrow> (\<exists>\<pi>. word cfg c \<pi> c' \<and> eff_list \<pi> s = Some s')"
  by (rule Submission.eq_path)

end