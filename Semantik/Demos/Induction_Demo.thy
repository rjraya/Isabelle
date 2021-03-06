theory Induction_Demo
imports Main
begin

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

(*
thm itrev.induct
thm itrev.simps

fun sep :: "'a \<Rightarrow>'a list \<Rightarrow> 'a list" where
"sep a (x#y#zs) = x # a # sep a (y#zs)" |
"sep a xs = xs"

thm sep.simps
*)

lemma itrev_aux1: "\<forall> ys. itrev xs ys = rev xs @ ys"
apply(induction xs)
apply(auto)
done

lemma itrev_aux2: "itrev xs ys = rev xs @ ys"
apply(induction xs arbitrary: ys)
apply(auto)
done

lemma "itrev xs [] = rev xs" by (auto simp: itrev_aux1)


(* Standard Example: fold *)

lemma "fold Cons xs ys = rev xs@ys" by (induction xs arbitrary: ys) auto
  
definition "f xs = fold (+) xs 0"

lemma aux1: "a + fold (+) ys (b::nat) = fold (+) ys (a+b)"
apply (induction ys arbitrary: b)
apply (auto simp: algebra_simps)
done

thm fold_append (* Auto will apply this theorem *)
  
lemma "f (xs@ys) = f xs + f (ys::nat list)"
unfolding f_def
apply (auto simp: aux1)
done 


subsection{* Computation Induction *}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

thm sep.induct

lemma "map f (sep a xs) = sep (f a) (map f xs)"
apply(induction a xs rule: sep.induct)
apply auto
done

hide_const f

fun zipf where
"zipf f [] [] = []" |
"zipf f (x#xs) (y#ys) = f x y # zipf f xs ys" |
"zipf _ _ _ = []"

lemma "length xs = length ys \<Longrightarrow> length (zipf f xs ys) = length ys"
apply(induction f xs ys rule: zipf.induct)
apply(auto)
done
  
(* We show that zipf is a generalization of the well-known zip function *)

lemma "zipf Pair xs ys = zip xs ys"
  (* If parameter is not variable, explicit type specification required! 
     in this case, Pair would get the most general type, with 'c and 'd 
     base types
  *)
  apply (induction "Pair::'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b)" 

         "xs::'a list" "ys::'b list" rule: zipf.induct)
  by auto
  

end
