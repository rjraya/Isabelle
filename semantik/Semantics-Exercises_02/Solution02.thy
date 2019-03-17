theory Solution02
imports "HOL-IMP.AExp"
begin

(* Induction *)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

text \<open>We already proved the following lemma connecting @{term itrev} and @{term rev}:\<close>
lemma itrev_rev:
  "itrev xs ys = rev xs @ ys"
  by (induction xs arbitrary: ys) auto

text \<open>In the last homework, you already defined \<open>fold_right\<close> on lists. Here is a left version of it:\<close>
fun fold_left :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold_left _ [] a = a"
| "fold_left f (x # xs) a = fold_left f xs (f x a)"

text \<open>Find and prove an appropriate theorem that connects \<open>itrev\<close> and \<open>fold_left\<close>,
and then use it to prove \<open>fold_left_rev\<close>.\<close>

lemma itrev_fold_left':
  "fold_left (#) xs ys = itrev xs ys"
  by (induction xs arbitrary: ys) auto

lemma itrev_fold_left:
  "fold_left (#) xs [] = itrev xs []"
  by (rule itrev_fold_left')

lemma fold_left_rev:
  "fold_left (#) xs [] = rev xs"
  by (simp add: itrev_fold_left itrev_rev)

text \<open>Define a function \<open>deduplicate\<close> that removes duplicate occurrences of subsequent elements.\<close>
fun deduplicate :: "'a list \<Rightarrow> 'a list" where
  "deduplicate [] = []"
| "deduplicate [x] = [x]"
| "deduplicate (x # y # xs) = (if x = y then deduplicate (y # xs) else x # deduplicate (y # xs))"

value "deduplicate [1,1,2,3,2,2,1::nat] = [1,2,3,2,1]"

text \<open>Prove that a deduplicated list has at most the length of the original list:\<close>
lemma
  "length (deduplicate xs) \<le> length xs"
(*
  apply (induction xs)
   apply auto
  subgoal for a xs
    apply (cases xs)
     apply auto
    done
  done
*)
  by (induction xs rule: deduplicate.induct) auto

(* substitution lemma *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a' (N n) = N n" |
"subst x a' (V y) = (if x=y then a' else V y)" |
"subst x a' (Plus a1 a2) = Plus (subst x a' a1) (subst x a' a2)"

lemma subst_lemma: "aval (subst x a' a) s = aval a (s(x:=aval a' s))"
  by (induction a) auto

lemma comp: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
  by (simp add: subst_lemma)

(* arithmetic expressions with side-effects and exceptions *)

datatype aexp' =
  N' int | V' vname | Plus' aexp' aexp' | \<comment>\<open>constructors as in @{typ aexp}\<close>
  PI' vname                               \<comment>\<open>new: postfix increment\<close>

fun aval' where
  "aval' (N' n) s = (n,s)" |
  "aval' (V' x) s = (s x,s)" |
  "aval' (PI' x) s = (s x,s(x:=s x+1))" |
  "aval' (Plus' a1 a2) s = (
    let (v1,s') = aval' a1 s; (v2,s'') = aval' a2 s' in (v1+v2,s'')
  )"

text \<open>
  Test your function for some terms. Is the output as expected?
  Note: \<open><>\<close> is an abbreviation for the state that assigns every
  variable to zero:
  @{thm [display] null_state_def[where 'b=int, no_vars]}
\<close>
value "<>(x:=0)"
value "aval' (Plus' (PI' ''x'') (V' ''x'')) <>"
value "aval' (Plus' (Plus' (PI' ''x'') (PI' ''x'')) (PI' ''x'')) <>"

text \<open>
  Is the plus-operation still commutative? Prove or disprove!
\<close>
lemma "aval' (Plus' (PI' x) (V' x)) <> \<noteq> aval' (Plus' (V' x) (PI' x)) <>"
  by auto

lemma aval'_inc': "aval' a s = (v,s') \<Longrightarrow> s x \<le> s' x"
  apply (induct a arbitrary: s s' v)
     apply (auto split: prod.splits)
  apply fastforce
  (* OR:
  apply (blast intro: order_trans)+
    OR:
  apply force+
  *)
  done

lemma aval'_inc:
  "aval' a <> = (v, s') \<Longrightarrow> 0 \<le> s' x"
  using aval'_inc' by (fastforce simp: null_state_def)

text \<open>
  Hint: If \<open>auto\<close> on its own leaves you with an \<open>if\<close> in the
  assumptions or with a \<open>case\<close>-statement, you should modify it like
  this: (\<open>auto split: if_splits prod.splits\<close>).
\<close>

(* variables of expression *)

fun vars :: "aexp \<Rightarrow> vname set" where
"vars (N _) = {}" |
"vars (V x) = {x}" |
"vars (Plus a1 a2) = vars a1 \<union> vars a2"

lemma ndep: "x \<notin> vars e \<Longrightarrow> aval e (s(x:=v)) = aval e s"
  by (induction e) auto

end