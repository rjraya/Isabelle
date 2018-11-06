theory Ex03
  imports "HOL-IMP.ASM"
begin

text \<open> Reflexive Transitive Closure \<close>

(* Universal predicate *)

inductive P :: "'a \<Rightarrow> bool" where "P x"

thm P.cases

lemma "P x"
apply(rule P.intros)
done

(* The empty predicate *)
inductive P1 :: "'a \<Rightarrow> bool"

thm P1.cases

lemma "\<not> P1 x"
apply(auto)
apply(cases rule: P1.cases)
apply assumption
done

(* for R enforces R to be fixed in all definition *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for R where
refl: "star R x x" |
step: "star R x y \<Longrightarrow>  R y z \<Longrightarrow>  star R x z"

lemma "star R x y \<Longrightarrow> R y z \<Longrightarrow> star R x z"
apply(rule star.intros)
apply assumption+
done

lemma star_prepend: "\<lbrakk>star R y z ; R x y \<rbrakk> \<Longrightarrow> star R x z"
apply(induction rule: star.induct)
(*apply(auto intro: star.intros)*)
(* ?y2 is an schematic that depends on xa
   ?y2 = \<lambda> xa.x*)
(* intro rule are something with assumptions and conclusion
   you want the tool to match its parts *)
apply(rule step)
apply(rule refl)
apply(assumption)
apply(rule step)
apply(assumption)
apply(assumption)
done

lemma star_append: "\<lbrakk> star r x y; r y z \<rbrakk> \<Longrightarrow> star r x z"
  by(rule star.intros)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for R where
refl': "star' R x x" |
step': "R x y \<Longrightarrow> star' R y z \<Longrightarrow>  star' R x z"

lemma star'_prepend: "\<lbrakk> star' r y z; r x y \<rbrakk> \<Longrightarrow> star' r x z"
  by(rule step')

lemma star'_append:"\<lbrakk> star' r x y; r y z \<rbrakk> \<Longrightarrow> star' r x z"
apply(induction rule: star'.induct)
apply(auto intro: star'.intros)
done

lemma "star r x y \<longleftrightarrow> star' r x y"
  apply auto
  apply(induction rule: star.induct)
  apply(auto intro: star'.intros)
  (* need to append in the back *)
  apply(rule star'_append)
  apply assumption+
  apply(induction rule:star'.induct)
  apply(auto intro: star.intros star_prepend)
done

text \<open>  Avoiding Stack Underflow \<close>

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk  = (Some (n # stk))" |
"exec1 (LOAD x) s stk  = (Some (s x # stk))" |
"exec1 ADD _ (i # j # stk)  = (Some ((i + j) # stk))" |
"exec1 ADD _ _ = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = (Some stk)" |
"exec (i#is) s stk = (case (exec1 i s stk) of 
  None \<Rightarrow> None |
  Some stk \<Rightarrow> exec is s stk)"

lemma exec_append[simp]: 
 "exec (is1@is2) s stk = (case exec is1 s stk of 
   Some stk' \<Rightarrow>  exec is2 s stk' |
   None \<Rightarrow> None)"
  apply(induction is1 arbitrary: stk)
  apply(auto split:option.splits)
done


theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
  apply(induction a arbitrary: stk)
  apply(auto)[]
  apply(auto)[]
  apply auto
  apply (subst exec_append)
  apply(auto split: option.splits)
done

lemma "(exec is1 s stk) = (Some stk') \<Longrightarrow> exec (is1@is2) s stk = exec is2 s stk'"


end