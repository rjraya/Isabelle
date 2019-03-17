theory Check
  imports Submission
begin

theorem S_T:
  "S xs \<Longrightarrow> T xs"
  by (rule Submission.S_T)

theorem T_S:
  "T xs \<Longrightarrow> count xs Open = count xs Close \<Longrightarrow> S xs"
  by (rule Submission.T_S)

theorem cmp_correct: "cmp a r = (x, prog) \<Longrightarrow>
  op_val x (execs prog \<sigma>) = aval a (\<sigma> o Var) \<and> execs prog \<sigma> o Var = \<sigma> o Var"
\<comment> \<open>The first conjunct states that the resulting operand contains the correct value,
    and the second conjunct states that the variable state is unchanged.\<close>
  by (rule Submission.cmp_correct)

theorem ex_split_has_split[code]:
  "ex_split P xs \<longleftrightarrow> has_split P [] xs"
  by (rule Submission.ex_split_has_split)

theorem linear_correct:
  "linear_split xs \<longleftrightarrow> ex_balanced_sum xs"
  by (rule Submission.linear_correct)

end