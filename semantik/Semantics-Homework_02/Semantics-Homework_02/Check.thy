theory Check
  imports Submission
begin

text \<open>Test cases for @{term denc}:\<close>
lemma
  "denc 0 [1,2,4,8] = [1,1,2,4]"
  "denc 0 [3,4,5] = [3,1,1]"
  "denc 0 [5] = [5]"
  "denc 0 [] = []"
  by simp+

lemma decode_code:
  "ddec 0 (denc 0 l) = l"
  by (rule Submission.decode_code)

lemma bval_beq:
  "bval (beq a1 a2) s \<longleftrightarrow> aval a1 s = aval a2 s"
  by (rule Submission.bval_beq)

lemma models_correct:
  "sat \<phi> \<sigma> \<longleftrightarrow> \<sigma> \<in> models \<phi>"
  by (rule Submission.models_correct)

lemma simplify_simplifies: "simplified (simplify \<phi>)"
  by (rule Submission.simplify_simplifies)

lemma simplify_correct: "models (simplify \<phi>) = models \<phi>"
  by (rule Submission.simplify_correct)

end