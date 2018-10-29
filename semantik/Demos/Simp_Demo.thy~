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
apply(simp add: algebra_simps)
done

text{* Giving a lemma the simp-attribute: *}
declare algebra_simps [simp]


subsection{* Rewriting with definitions *}

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n*n"

lemma "sq(n*n) = sq(n)*sq(n)"
apply(simp add: sq_def) (* Definition of function is implicitly called f_def *)
done

subsection{* Case distinctions *}

text{* Automatic: *}
lemma "(A & B) = (if A then B else False)"
apply(simp)
done

lemma "if A then B else C"
apply(simp)
oops

text{* By hand (for case): *}
lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
apply(simp split: list.split)
done

subsection {* Arithmetic *}

text{* A bit of linear arithmetic (no multiplication) is automatic: *}
lemma "\<lbrakk> (x::nat) \<le> y+z;  z+x < y \<rbrakk> \<Longrightarrow> x < y"
apply(simp)
done


subsection{* Tracing: *}

lemma "rev[x] = []"
using [[simp_trace]] apply(simp)
oops

text{* Method ``auto'' can be modified almost like ``simp'': instead of
``add'' use ``simp add'': *}

end
