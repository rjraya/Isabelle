theory Defs
imports Main
begin

inductive is_path :: "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool"
for E where
  NilI: "is_path E u [] u"
| ConsI: "\<lbrakk> E u v; is_path E v l w \<rbrakk> \<Longrightarrow> is_path E u (u#l) w"

fun path :: "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
  "path E u [] v \<longleftrightarrow> v = u" |
  "path E u [v] w \<longleftrightarrow> u = v \<and> E v w" |
  "path E u (x # y # xs) v \<longleftrightarrow> (u = x \<and> E x y \<and> path E y (y # xs) v)"

lemma path_Nil: "is_path E u [] v \<longleftrightarrow> u=v"
  by (auto intro: is_path.intros elim: is_path.cases)

lemma path_Cons: "is_path E u (v#p) w \<longleftrightarrow> 
  (\<exists>vh. u=v \<and> E v vh \<and> is_path E vh p w)"
  by (auto intro: is_path.intros elim: is_path.cases)

end