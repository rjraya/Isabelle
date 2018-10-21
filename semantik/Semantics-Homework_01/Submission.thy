theory Submission
  imports Defs
begin

text \<open>Define \<open>fold_right\<close> here:\<close>

fun fold_right :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a" where
"fold_right _ [] a = a" |
"fold_right f (x # xs) a = (f x (fold_right f xs a))"

text \<open>Test cases for \<open>fold_right\<close>\<close>
value "fold_right (+) [1,2,3] (4 :: nat) = 10"
value "fold_right (#) [a,b,c] [] = [a,b,c]"

text \<open>
  Prove that \<open>fold_right\<close> applied to the result of \<open>map\<close>
  can be contracted into a single \<open>fold_right\<close>:
\<close>
lemma fold_right_map:
  "fold_right f (map g xs) a = fold_right (f o g) xs a"
apply(induction xs)
apply(auto)
done

text \<open>Prove the following lemma on \<open>fold_right\<close> and \<open>append\<close>:\<close>
lemma fold_right_append:
  "fold_right f (xs @ ys) a = fold_right f xs (fold_right f ys a)"
apply(induction xs)
apply(auto)
done

text \<open>
  For the remainder of the homework we will consider the special case where \<open>f\<close>
  is the addition operation on natural numbers.
  Prove that sums over natural numbers can be ``pulled apart'':
\<close>
lemma fold_right_sum_append:
  "fold_right (+) (xs @ ys) (0 :: nat) = fold_right (+) xs 0 + fold_right (+) ys 0"
apply(induction xs)
apply(auto)
done

text \<open>
  Finally prove that calculating the sum from the right and from the left yields the same result:
\<close>

lemma fold_right_snoc [simp]:
  "fold_right (+) (snoc l a) (x :: nat) = a + fold_right (+) l x"
  apply(induction l)
  apply(auto)
done

lemma fold_right_sum_reverse:
  "fold_right (+) (reverse xs) (x :: nat) = fold_right (+) xs x"
  apply(induction xs)
  apply(auto)
done

end