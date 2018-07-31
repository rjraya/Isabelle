theory Exercises2
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where 
"contents Tip = []" |
"contents (Node l a r) = contents l @ [a] @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where 
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + sum_tree l + sum_tree r"

lemma "sum_tree t = sum_list (contents t)" 
apply(induction t)
apply(auto)
done

datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf a) = (Leaf a)" |
"mirror (Node l a r) = (Node (mirror r) a (mirror l))"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf a) = [a]" |
"pre_order (Node l a r) = [a] @ pre_order(l) @ pre_order(r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where 
"post_order (Leaf a) = [a]" |
"post_order (Node l a r) = post_order(l) @ post_order(r) @ [a]"

lemma "pre_order (mirror t) = rev (post_order t)"
apply(induction t)
apply(auto)
done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # xs) = x # (a # (intersperse a xs))"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs)
apply(auto)
done

end





