theory Defs
  imports "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/Big_Step"

begin

class vars = fixes vars :: "'a \<Rightarrow> vname set"

instantiation aexp :: vars
begin
fun vars_aexp :: "aexp \<Rightarrow> vname set" where
"vars (N n) = {}" |
"vars (V x) = {x}" |
"vars (Plus a\<^sub>1 a\<^sub>2) = vars a\<^sub>1 \<union> vars a\<^sub>2"
instance ..
end

instantiation bexp :: vars
begin
fun vars_bexp :: "bexp \<Rightarrow> vname set" where
"vars (Bc v) = {}" |
"vars (Not b) = vars b" |
"vars (And b\<^sub>1 b\<^sub>2) = vars b\<^sub>1 \<union> vars b\<^sub>2" |
"vars (Less a\<^sub>1 a\<^sub>2) = vars a\<^sub>1 \<union> vars a\<^sub>2"
instance ..
end

instantiation com :: vars
begin
fun vars_com :: "com \<Rightarrow> vname set" where
 "vars_com  SKIP = {}"
|"vars_com (x ::= a) = {x} \<union> vars a"
|"vars_com (c1 ;; c2) = vars_com c1 \<union> vars_com c2"
|"vars_com (IF b THEN c1 ELSE c2) = vars b \<union> vars_com c1 \<union> vars_com c2"
|"vars_com (WHILE b DO c) = vars b \<union> vars_com c"
instance ..
end

end