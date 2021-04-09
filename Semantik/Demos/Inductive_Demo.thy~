theory Inductive_Demo
imports Main
begin

subsection{*Inductive definition of the even numbers*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS
thm ev.intros

text{* Using the introduction rules: *}

(* proof backward *)
lemma "ev (Suc(Suc(Suc(Suc 0))))"
  apply(rule evSS)
  apply(rule evSS)
by(rule ev0)

(* proof forward *)
thm ev0
thm evSS[OF ev0]
thm evSS[OF evSS[OF ev0]]

text{* A recursive definition of evenness: *}
fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text{*A simple example of rule induction: *}
lemma "ev n \<Longrightarrow> evn n"
apply(induction rule: ev.induct)
by auto

text{* An induction on the computation of evn: *}
lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
(* apply(auto intro: ev.intros) or *)
apply(auto intro: ev0 evSS)
done

text{* No problem with termination because the premises are always smaller
than the conclusion: *}
(* evSS is a conditional rewrite rule *)
declare ev.intros[simp,intro]

text{* A shorter proof: *}
lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
apply(simp_all)
done

text{* The power of arith: *}
lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
apply(induction rule: ev.induct)
apply(auto)
(* try0 *)
apply(arith)
done

subsection{*Inductive definition of the reflexive transitive closure *}

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
(* considered bad style, just rename the variables*)
apply(rename_tac x0 x1 x2)
  apply(simp)
  (*apply(blast intro: step)*)
  (*apply(rule step) apply assumption apply assumption*)
   (*apply(rule step) apply assumption+
     + iterates the method as long as it does not fail*)
  by (rule step)
  (*by does simp and then the applies, transitively 
    discharging implications*)
done

end
