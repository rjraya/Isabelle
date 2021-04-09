theory Ex01
imports Main
begin

value "2 + (2 ::nat)"
value "(2 ::nat) * (5 + 3)"
value "(3 ::nat) * 4 - 2 * (7 + 1)"
(* doesnt go below zero *)

lemma "(a :: nat) + 0 = a" by (rule Nat.add_0_right)
lemma conmutativity: "(a :: nat) + b = b + a" by (rule  Groups.ab_semigroup_add_class.add.commute)
(* or by simp *)
lemma associativity: "((a :: nat) + b) + c = a + (b + c)" by (rule  Groups.ab_semigroup_add_class.add_ac(1))

(*
lemma associativity:
  fixes a b c :: nat
  shows "a + b + c = a + (b + c)"
  apply simp
done
*)

fun count :: "'a list \<Rightarrow> 'a  \<Rightarrow> nat" where
"count [] _ = 0" | 
"count (x # xs) a = (if(x = a) then Suc (count xs a) else count xs a)"
(* Isabelle doesn't allow pattern matching in arguments lists" *)

value "count [1 :: nat,2,3] 1"
value "count [1 :: nat, 1, 2, 3] 1"
value "count [1 :: nat, 2, 3] 2"
(* lemma "count [1,2,2,3] (1 :: nat)" by simp *)

lemma decrease_length: "(count xs x) \<le> (length xs)"
apply(induction xs)
apply(auto)
  done 

lemma "count xs x \<le> length xs"
  apply(induction xs)
  apply(subst count.simps,simp)
  apply simp
done

lemma "count xs x \<le> length xs"
  apply(induction xs)
  apply(simp)
  apply(simp)
done

(*
   the proof does here a case distinction and  
   then considers the if-else
*)

(* auto takes all subgoals at same time and
   simp takes one subgoal at a time*)


(* *)
thm count.simps

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (x # xs) y = x # (snoc xs y)"

value "snoc [] c"
value "snoc [a,b,c] c"

lemma "snoc [] c = [c]" by auto
lemma "snoc [a,b,c] c = [a,b,c,c]" by auto
(* or by simp *)

fun reverse :: "'a list \<Rightarrow> 'a list" where 
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "reverse [a,b,c]"
value "reverse [1 :: int, 2]"
lemma "reverse [a,b,c] = [c,b,a]" by auto 

(* 
 lemma "snoc((reverse xs) a) = reverse(a # xs)" 
 this lemma leads to not being able to apply 
 induction hypotheses
*)
lemma rev_snoc [simp] : "reverse ( snoc xs x ) = x # ( reverse xs )"
  apply(induction xs)
  apply(simp)
  (* apply(simp) *)
  apply(subst snoc.simps)
  apply(subst reverse.simps)
  (* apply(auto) *)
  apply(simp)
done

theorem "reverse (reverse xs) = xs" 
  apply(induction xs)
  apply(auto)
done

end