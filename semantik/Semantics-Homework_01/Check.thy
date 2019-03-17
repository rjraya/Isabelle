theory Check
  imports Submission
begin

text \<open>We make sure that your definition of \<open>fold_right\<close> passes the test cases:\<close>

lemma
  "fold_right (+) [1,2,3] (4 :: nat) = 10"
  by simp

lemma
  "fold_right (#) [a,b,c] [] = [a,b,c]"
  by simp

text \<open>And we check that you proved the right theorems:\<close>

lemma fold_right_map:
  "fold_right f (map g xs) a = fold_right (f o g) xs a"
  by (rule Submission.fold_right_map)

lemma fold_right_append:
  "fold_right f (xs @ ys) a = fold_right f xs (fold_right f ys a)"
  by (rule Submission.fold_right_append)

lemma fold_right_sum_append:
  "fold_right (+) (xs @ ys) (0 :: nat) = fold_right (+) xs 0 + fold_right (+) ys 0"
  by (rule Submission.fold_right_sum_append)

lemma fold_right_sum_reverse:
  "fold_right (+) (reverse xs) (x :: nat) = fold_right (+) xs x"
  by (rule Submission.fold_right_sum_reverse)

end