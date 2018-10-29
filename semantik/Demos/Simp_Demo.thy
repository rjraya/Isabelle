theory Simp_Demo
imports Main
begin

section{* How to simplify *}

text{* No assumption: *}
lemma "ys @ [] = []"
apply(simp)
oops (* abandon proof *)

text{* Simplification in assumption: *}
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
apply(simp)
done

text{* Using additional rules: *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
(* adds lemmas on multiplication and addition *)
apply(simp add: algebra_simps) 
done

text{* Giving a lemma the simp-attribute: *}
declare algebra_simps [simp]
(* You can see the rules this way *)
(* lemmas [simp] = algebra_simps *)

subsection{* Rewriting with definitions *}

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n*n"

(* If simp cannot simplify anything, it will fail *)
lemma "sq(n*n) = sq(n)*sq(n)"
(* 
(* other way *)
unfolding sq_def
apply simp
*)
apply(simp add: sq_def) (* Definition of function is implicitly called f_def *)
done

subsection{* Case distinctions *}

text{* Automatic: *}
lemma "(A & B) = (if A then B else False)"
  apply(simp)
(*if you apply auto, it will give two subgoals*)
done

lemma "if A then B else C"
apply(simp)
oops

text{* By hand (for case): *}
lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
apply(simp split: list.split)
done

(* examples where assumptions contain case distinction,add missing theorems! *)

text \<open> If case occurs in assumptions \<close>

lemma "(case xs of [] \<Rightarrow> 0::nat | x#xs' \<Rightarrow> x) > 0 \<Longrightarrow> hd xs \<noteq> 0"
  apply (simp split: list.split_asm)
  done

text \<open> \<open>list.splits = list.split list.split_asm\<close>, and similar for other datatypes \<close>   
  
lemma "(case xs of [] \<Rightarrow> 0::nat | x#xs' \<Rightarrow> x) > 0 \<Longrightarrow> hd xs \<noteq> 0"
  by (simp split: list.splits)
  
text \<open>If no special reason against: Just use \<open>.splits\<close> - lemma! \<close>


subsection {* Arithmetic *}

text{* A bit of linear arithmetic (no multiplication) is automatic: *}
lemma "\<lbrakk> (x::nat) \<le> y+z;  z+x < y \<rbrakk> \<Longrightarrow> x < y"
(*
  automatically
  try0
  by simp
*)
apply(simp)
done


subsection{* Tracing: *}

(*
logging output of the simplifier
declare [[simp_trace]]
*)


lemma "rev[x] = []"
  (* better use locally the trace otherwise you block the system *)
  supply [[simp_trace]] apply(simp)
oops

text{* Method ``auto'' can be modified almost like ``simp'': instead of
``add'' use ``simp add'': *}

thm nth_append

lemma "i < length xs \<Longrightarrow> (xs@ys)!i = xs!i"
apply (auto simp: nth_append)
done

end
