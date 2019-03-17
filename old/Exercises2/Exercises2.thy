theory Exercises2
imports Main
begin

(* This file contains different computers contents, needs to be reviewed *)

(* Exercise 2.1 *)

value "1+(2::nat)"
value "1+(2::int)"
value "1-(2::nat)"
value "1-(2::int)"

(* 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma nSm_Snm[simp]: "add n (Suc m) = add (Suc n) m"
apply (induction n)
apply (auto)
done 

(* 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem add_itadd: "itadd m n = add m n"
apply (induction m arbitrary: n)
apply (auto)
done

(* Exercise 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

(* 
   It would be nice to define the second case as add m (Suc n)
   but in that case, how would we prove add_assoc? 

   Instead we later prove lemma add_succ which needs to be 
   reused in several proofs
*)

lemma add_assoc: "add (add a b) c = add a (add b c)"
apply(induction a)
apply(auto)
done

lemma add_neutral: "add m 0 = m"
apply(induction m)
apply(auto)
done

lemma add_succ: "Suc (add a b) = add a (Suc b)"
apply(induction a)
apply(auto)
done

lemma add_commutative : "add a b = add b a"
apply(induction a)
apply(auto simp add: add_succ add_neutral)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc(Suc(double n))"

lemma double_add: "double m = add m m"
apply(induction m)
apply(auto simp add: add_succ)
done

(* Exercise 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a [] = 0" | 
"count a (x # xs) = (if(x = a) then Suc (count a xs) else count a xs)"

lemma decrease_length: "(count x xs) \<le> (length xs)"
apply(induction xs)
apply(auto)
done 

(* Exercise 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = [x]" |
  "snoc (x # xs) y = x # ( snoc xs y )"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil" |
  "reverse ( x # xs ) = snoc ( reverse xs ) x"

lemma rev_snoc [simp] : "reverse ( snoc xs x ) = x # ( reverse xs )"
apply ( induction xs )
apply ( auto )
done

theorem rev_rev : "reverse ( reverse xs ) = xs"
apply ( induction xs )
apply ( auto )
  done

(* Exercise 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = (Suc n) + (sum_upto n)"

lemma gauss: "sum_upto n = (n * (n + 1)) div 2"
apply(induction n)
apply(auto)
  done 


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

(* Exercise 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

value "add (3 :: nat) (4 :: nat)"

lemma "itadd m n = add m n"
apply(induction m arbitrary: n)
apply(auto simp add: add_succ)
done

(* Exercise 2.10 *) 

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

(* Solving the linear recurrence gives 2^n(t+1)-1 *)

lemma "nodes (explode n t) = 2^n*(nodes t+1)-1"
apply(induction n arbitrary: t)
apply(auto simp add: algebra_simps)
done

(* Exercise 2.11 *) 

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const x) y = x" |
"eval (Add x y) z = (eval x z) + (eval y z)" |
"eval (Mult x y) z = (eval x z) * (eval y z)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (x # xs) y = x + y*evalp xs y"

fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"addp [] xs = xs" |
"addp xs [] = xs" |
"addp (x # xs) (y # ys) = (x + y) # addp xs ys"

fun smultp :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"smultp k [] = []" |
"smultp k (x # xs) = k * x # smultp k xs"

fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"multp [] xs = []" |
"multp (x # xs) ys = addp (smultp x ys) (0 # multp xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const k) = [k]" |
"coeffs (Add p q) = addp (coeffs p) (coeffs q)" |
"coeffs (Mult p q) = multp (coeffs p) (coeffs q)"

lemma evalp_additive: "evalp (addp xs ys) a = evalp xs a + evalp ys a"
apply (induction rule:addp.induct)
apply (auto simp add:Int.int_distrib)
done

lemma eval_preserves_mult: "evalp (smultp x ys) a = x * evalp ys a"
apply (induction ys)
apply (auto simp add:Int.int_distrib)
done 

lemma evalp_multiplicative[simp]: "evalp (multp xs ys) a = evalp xs a * evalp ys a"
apply (induction xs)
apply (auto simp add:Int.int_distrib evalp_additive eval_preserves_mult)
done 

lemma evalp_eval: "evalp (coeffs e) x = eval e x"
apply (induction e)
apply (auto simp add: evalp_additive)
done

end





