theory Check
  imports Submission
begin

theorem ex2:
  "no c \<Longrightarrow> \<forall> s. \<exists> t. (c, s) \<Rightarrow> t"
  by (rule Submission.ex2)

theorem AA_gen_kill: "AA c A = (A \<union> gen c) - kill c"
  by (rule Submission.AA_gen_kill)

theorem AA_sound:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> \<forall> (x,y) \<in> A. s x = s y \<Longrightarrow> \<forall> (x,y) \<in> AA c A. s' x = s' y"
  by (rule Submission.AA_sound)

theorem CP_correct1:
  assumes "(c, s) \<Rightarrow> t" "\<forall>(x,y)\<in>A. s x = s y"
  shows   "(CP c A, s) \<Rightarrow> t"
  using assms by (rule Submission.CP_correct1)

theorem CP_correct2:
  assumes "(CP c A, s) \<Rightarrow> t" "\<forall>(x,y)\<in>A. s x = s y"
  shows "(c, s) \<Rightarrow> t"
  using assms by (rule Submission.CP_correct2)

end