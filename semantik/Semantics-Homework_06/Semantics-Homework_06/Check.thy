theory Check
  imports Submission
begin

theorem square_correct: "s ''n'' \<equiv> n \<Longrightarrow> n \<ge> 0 \<Longrightarrow> wlp square (\<lambda>s'. let a = s' ''a'' in a = n*n) s"
  by (rule Submission.square_correct)

theorem small_step_cfg_step: "cs \<rightarrow> cs' \<Longrightarrow> cfg_step cs = cs'"
  by (rule Submission.small_step_cfg_step)

theorem final_cfg_step: "final cs \<Longrightarrow> cfg_step cs = cs"
  by (rule Submission.final_cfg_step)

theorem small_steps_cfg_steps:
  "cs \<rightarrow>* cs' \<Longrightarrow> \<exists>n. cfg_steps n cs = cs'"
  by (rule Submission.small_steps_cfg_steps)

theorem cfg_steps_small_steps:
  "cfg_steps n cs = cs' \<Longrightarrow> cs \<rightarrow>* cs'"
  by (rule Submission.cfg_steps_small_steps)

theorem terminating_simulation:
  assumes "is_sim R step step'" "terminating step' b" "R a b"
  shows "terminating step a"
  using assms by (rule Submission.terminating_simulation)

theorem wlp_whileI':
  assumes INIT: "I s\<^sub>0"
  assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp c I s else Q s)"
  shows "wlp (WHILE b DO c) Q s\<^sub>0"
  using assms by (rule Submission.wlp_whileI')

end