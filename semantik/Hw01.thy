theory Hw01
imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc: "reverse (snoc xs y) = y # reverse xs"
by (induct xs) auto

theorem reverse_reverse: "reverse (reverse xs) = xs"
  by (induct xs) (auto simp add: reverse_snoc)


fun fold_right :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a" where
"fold_right _ [] a = a" |
"fold_right f (x # xs) a = (f x (fold_right f xs a))"

value "fold_right (op +) [1,2,3] (4::nat) = 10"
value "fold_right (op #) [a,b,c] [] = [a,b,c]"

lemma fold_right_map: 
 "fold_right f (map g xs) a = fold_right (f o g) xs a" 
apply(induction xs)
apply(auto)
done

lemma fold_right_append:
 "fold_right f (xs @ ys) a = fold_right f xs (fold_right f ys a)"
apply(induction xs)
apply(auto)
done

lemma fold_right_sum_append:
  "fold_right (op +) (xs @ ys) (0 :: nat) = 
  fold_right (op +) xs 0 + fold_right (op +) ys 0"
apply(induction xs)
apply(auto)
done

lemma fold_right_sum_reverse:
 "fold_right (op +) (reverse xs) (x :: nat) = 
  fold_right (op +) xs x"


end