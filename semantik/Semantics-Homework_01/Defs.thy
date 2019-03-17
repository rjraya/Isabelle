theory Defs
  imports Main
begin

text \<open>Definitions and lemmas from the tutorial\<close>

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

end