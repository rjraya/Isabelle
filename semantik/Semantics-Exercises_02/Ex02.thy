theory Ex02
  imports Main "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

(* Exercise 1 modify to use itrev*)
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

fun fold_left :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
"fold_left _ [] a = a"
| "fold_left f (x#xs) a = fold_left f xs (f x a)"

lemma fold_general: "fold_left (#) xs b = rev xs @ b"
apply(induction xs arbitrary: b)
apply(auto)
done

lemma fold_left_rev: "fold_left (#) xs [] = rev xs"
apply(simp add: fold_general)
done

(*
his solution
fold_left (#) xs ys = itrev xs ys"
apply (induction xs arbitrary:ys
apply auto
done
lemma fold_left(#) xs [] = rev xs
apply(simp add: fold_left_itrev itrev_rev)
done

the way to apply a lemma one step is use
apply(susbst fold_left_itrev)
apply(subst itrev_rev
apply simp
*)

fun deduplicate :: "'a list \<Rightarrow> 'a list" where
"deduplicate (x#y#xs) = 
  (if x = y then x#(deduplicate xs) else x#y#(deduplicate xs))"
| "deduplicate xs = xs"

value "deduplicate [1,1,2,3,2,2,1::nat] = [1,2,3,2,1]"

lemma dedu_length: "length (deduplicate xs) \<le> length xs"
apply(induction xs rule: deduplicate.induct)
apply(auto)
  done

(*
His solution
fun deduplicate :: "a'list\<Rightarrow> 'a list where
"deduplicate [] = []" |
"deduplicate [x] = [x]" \
"deduplicate (x#y#xs) = 
(if x = y then deduplicate (y#xs) else x#deduplicate(y#xs))"

for the lemma

apply(induction xs)
apply auto
subgoal for x xs \<rightarrow> focus on this goal
 apply (cases xs) \<rightarrow> do a case distinction
 apply simp
 apply auto

*) 

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x t (N n) = (N n)" |
"subst x t (V y) = (if x = y then t else (V y))" |
"subst x t (Plus a1 a2) = Plus (subst x t a1) (subst x t a2)"

lemma subst_lemma [simp]: "aval (subst x a' a) s = aval a (s(x:=aval a' s))"
apply(induction a) 
(*
can be also done with subst.induct 
what happens now is
apply simp
apply simp (induction case)
apply(subst subst.simps) 
apply(subt aval.simps)
apply(subst aval.simps)
apply(simp)
*)
apply(auto)
done

(* 
interpret  
simpler solution apply(simp add: subst_lemma) we can see it
apply(subst subst_lemma)+ (+ means apply it two times)
*)

lemma comp: 
"aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
apply(induction a1 a2 rule: subst.induct)
apply(auto)
done

datatype aexp' = N' int | V' vname | Plus' aexp' aexp' | PI' vname

(* expressions can change state, this is why we add state as return value *)

(* useful let (a,b) = some_result in a + b *)

fun aval':: "aexp' \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
"aval' (N' n) s = (n, s)" |
"aval' (V' x) s = (s x, s)" |
"aval' (Plus' a1 a2) s = 
  (let (v1,s1) = aval' a1 s in 
   let (v2,s2) = aval' a2 s1 in
    (v1+v2,s2))" |
"aval' (PI' v) s = (s v,s(v := s v + 1))"

value "<>(x:=0)"
value "aval' (Plus' (PI' ''x'')(V' ''x'')) <>"
value "aval' (Plus' (Plus' (PI' ''x'') (PI' ''x'')) (PI' ''x'')) <>"

lemma "aval'(Plus' (PI' x) (V' x)) <> \<noteq> aval' (Plus' (V' x) (PI' x))  <>" by auto

(*
A proof method that is still incomplete but tries harder than auto is
fastforce. It either succeeds or fails, it acts on the first subgoal only, and it
can be modified like auto, e.g., with simp add.
*)

(* 
 This is a generalization for next lemma
*)
lemma aval'_inc': "aval' a s = (v,s') \<Longrightarrow> s x \<le> s' x"
apply (induct a arbitrary: s s' v)
apply (auto split: prod.splits)
apply fastforce
done

lemma aval'_inc: "aval' a <> = (v,s') \<Longrightarrow> 0 \<le> s' x"
  using aval'_inc' by (fastforce simp: null_state_def)

fun vars :: "aexp \<Rightarrow> vname set" where
"vars (N _) = {}" |
"vars (V x) = {x}" |
"vars (Plus a1 a2) = vars a1 \<union> vars a2"

lemma ndep: "x \<notin> vars e \<Longrightarrow> aval e (s(x:=v)) = aval e s"
  by (induction e) auto

end