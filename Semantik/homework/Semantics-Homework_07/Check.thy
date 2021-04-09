theory Check
  imports Submission
begin

theorem factorial_prog_correct:
 "HT (\<lambda>\<ss>. VAR \<ss> ''n'' ((\<le>) 0)) factorial_prog
  (\<lambda>\<ss>\<^sub>0. VAR \<ss>\<^sub>0 ''n'' (\<lambda>n\<^sub>0 \<ss>. VAR \<ss> ''a'' (\<lambda>a. a = factorial n\<^sub>0)))"
  by (rule Submission.factorial_prog_spec)

theorem fib_prog_correct:
 "HT (\<lambda>\<ss>. VAR \<ss> ''n'' ((\<le>) 0)) fib_prog (\<lambda>\<ss>\<^sub>0 \<ss>. VAR \<ss> ''n'' (\<lambda>n. VAR \<ss> ''a'' (\<lambda>a. a = fib n)))"
  by (rule Submission.fib_prog_spec)

theorem fib_prog'_correct:
 "HT (\<lambda>\<ss>. True) fib_prog' (\<lambda>\<ss>\<^sub>0. VAR \<ss>\<^sub>0 ''n'' (\<lambda>n\<^sub>0 \<ss>. VAR \<ss> ''a'' (\<lambda>a. a = fib n\<^sub>0)))"
  by (rule Submission.fib_prog'_spec)

theorem wp_strengthen_modset:
  "wp c Q s \<Longrightarrow> wp c (\<lambda>s'. Q s' \<and> (\<forall>x. x\<notin>lhsv c \<longrightarrow> s' x = s x)) s"
  by (rule Submission.wp_strengthen_modset)

end