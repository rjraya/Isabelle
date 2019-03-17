theory Auto_Proof_Demo
imports Main
begin

section{* Logic and sets *}

lemma "ALL x. EX y. x=y"
by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C"
by auto

text{* Note the bounded quantification notation: *}

(* force is better than auto instantiating quantifiers *)
lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk> \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce


text{*
 Most simple proofs in FOL and set theory are automatic.
 Example: if T is total, A is antisymmetric
 and T is a subset of A, then A is a subset of T.
*}

lemma AT:
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast


section{* Sledgehammer *}

(* ctrl-e <uparrow> to put the star on top *)
lemma "R^* \<subseteq> (R \<union> S)^*"
  (* find_theorems "_ \<subseteq> \<Longrightarrow> _^* \<subseteq> _^*"*)
  (*sledgehammer*)
  by (simp add: rtrancl_mono)


(* Find a suitable P and try sledgehammer: *)

lemma "a # xs = ys @ [a] \<longleftrightarrow> (\<exists>xs'. xs = xs'@[a] \<and> ys = a#xs') \<or> (xs = [] \<and> ys=[])"
  (*apply(rule exI[where x = ""])*)
  (*nitpick gives more useful counter-examples*)
  (*apply(cases ys; cases xs rule: rev_cases)
    the case splitting is performmed on lists but
    with empty list or a list with a last element
    try thm rev_cases*)
  (* heuristic: apply auto before sledgehammer *)
  apply auto
  by (metis Cons_eq_append_conv)
  (* subgoal sledgehammer sorry 
    to do something else in the meantime *)



section{* Arithmetic *}

(* many arithmetic is in simp *)
lemma "\<lbrakk> (a::int) \<le> f x + b; 2 * f x < c \<rbrakk> \<Longrightarrow> 2*a + 1 \<le> 2*b + c"
by arith

lemma "\<forall> (k::nat) \<ge> 8. \<exists> i j. k = 3*i + 5*j"
by arith

lemma "(n::int) mod 2 = 1 \<Longrightarrow> (n+n) mod 2 = 0"
by arith

lemma "(i + j) * (i - j) \<le> i*i + j*(j::int)"
by (simp add: algebra_simps)

(* 
   you do computation over lists of booleans, 
   which is a logarithmic representation
*)
lemma "(5::int) ^ 2 = 20+5"
by simp

end
