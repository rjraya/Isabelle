theory Experiment
  imports FOL
begin

(* These are some derivations from Paulson's
   The Foundation of a Generic Theorem Prover *)
ML_val \<open>Thm.lift_rule @{cterm "A \<and> B \<Longrightarrow> C \<longrightarrow> A \<and> C"} @{thm impI}\<close>

lemma and_lemma: "\<And> z. G(z) \<or> H(z)"
  ML_val \<open>#goal @{Isar.goal}\<close>
  ML_val \<open>Thm.prop_of (#goal @{Isar.goal})\<close>
  thm disjI1
  ML_val \<open>Thm.lift_rule (Thm.cprem_of (#goal @{Isar.goal}) 1) @{thm disjI1}\<close>
  sorry

lemma and_lemma': "\<forall> z. G(z) \<or> H(z)"
  sorry

(* Variables in Isabelle  *)
find_theorems "\<And> _ . _"
thm allI allE
ML_val \<open>@{term "x"}\<close>
ML_val \<open>@{term "\<And> z. G(z) \<or> H(z)"}\<close>
ML_val \<open>Thm.prop_of @{thm allI}\<close>
ML_val \<open>Thm.prop_of @{thm and_lemma}\<close>
ML_val \<open>@{term "\<forall>x. P(x)"}\<close>
ML_val \<open>Thm.forall_elim @{cterm "A"} @{thm allE}\<close>


end