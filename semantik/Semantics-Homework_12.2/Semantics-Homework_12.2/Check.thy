theory Check
  imports Submission
begin

theorem cnv_to_abs_correct: "cnv_to_abs P \<turnstile>\<^sub>a c \<rightarrow>* c' \<longleftrightarrow> P \<turnstile> c \<rightarrow>* c'"
  by (rule Submission.cnv_to_abs_correct)

theorem cnv_to_rel_correct: "P \<turnstile>\<^sub>a c \<rightarrow>* c' \<longleftrightarrow> cnv_to_rel P \<turnstile> c \<rightarrow>* c'"
  by (rule Submission.cnv_to_rel_correct)

end