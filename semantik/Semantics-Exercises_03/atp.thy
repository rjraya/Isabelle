theory atp
  imports "HOL-IMP.ASM"
begin

text \<open> Reflexive Transitive Closure \<close>

(* for R enforces R to be fixed in all definition *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for R where
ref[iff]: "star R x x" |
step: "R x y \<Longrightarrow> star R y z \<Longrightarrow>  star R x z"

lemma [intro]: "R x y \<Longrightarrow> star R x y" by (simp add: step)



end