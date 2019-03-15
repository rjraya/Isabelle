theory Seminar2
  imports Main
begin

text\<open>
 Logical and mathematical symbols

 For the purpose of this seminar just select the tab "Symbols" at
 the bottom left and see the tabs: "Logic", "Relation"...

 Set notation is also available. The main logic of Isabelle, HOL,
 works with arbitrarily nested sets quantified.
\<close>

section\<open>Logic and sets\<close>

lemma "\<forall> x. \<exists> y. x=y" by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C" by auto

text\<open>Note the bounded quantification notation:\<close>

lemma "\<lbrakk> \<forall>xs \<in> A. \<exists>ys. xs = ys @ ys;  us \<in> A \<rbrakk> 
        \<Longrightarrow> \<exists>n. length us = n+n"
by fastforce

text\<open>
 Most simple proofs in FOL and set theory are automatic.
 Example: if T is total, A is antisymmetric
 and T is a subset of A, then A is a subset of T.
\<close>

lemma AT:
  "\<lbrakk> \<forall>x y. T x y \<or> T y x;
     \<forall>x y. A x y \<and> A y x \<longrightarrow> x = y;
     \<forall>x y. T x y \<longrightarrow> A x y \<rbrakk>
   \<Longrightarrow> \<forall>x y. A x y \<longrightarrow> T x y"
by blast

section\<open>Sledgehammer\<close>

lemma "R^* \<subseteq> (R \<union> S)^*"
oops

text\<open>
 Intuition is needed:
 
 Find a suitable P and try sledgehammer: 
\<close>

lemma "a # xs = ys @ [a] \<longleftrightarrow> P"
oops


section\<open>Arithmetic\<close>

lemma "\<forall> (k::nat) \<ge> 8. \<exists> i j. k = 3*i + 5*j" by arith

text\<open>
 If unsure you can try method try0
\<close>
lemma "(n::int) mod 2 = 1 \<Longrightarrow> (n+n) mod 2 = 0" oops

text\<open>
 Special rules may be added to simp
\<close>
lemma "(i + j) * (i - j) \<le> i*i + j*(j::int)"
  by (simp add: algebra_simps)
thm algebra_simps

section\<open>Single step methods\<close>

thm conjI impI iffI notI

text\<open> 
 Instantiation of theorems: "of"

 of for substitution of variables by variables
\<close>

text\<open> Positional: \<close>
thm conjI[of "A" "B"] conjI[of "A"] conjI[of _ "B"]

text\<open> By name: \<close>
thm conjI[where ?Q = "B"]

text\<open> 
 Composition of theorems: OF 

 OF for substitutions of premises by theorems
\<close>

thm refl[of "a"] conjI
thm conjI[OF refl[of "a"]] conjI[OF _ refl[of "b"]]
thm conjI[OF refl[of "a"] refl[of "b"]]

section\<open>Inductive definitions\<close>

text\<open>
 How would you define the following notions in a functional language?
 
 1. Even/odd numbers 
 2. The reflexive transitive closure of a relation
 3. A terminating relation
\<close>

subsection\<open>Inductive definition of the even numbers\<close>

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS ev.intros
thm ev.induct

text\<open>Using the introduction rules: \<close>
lemma "ev (Suc(Suc(Suc(Suc 0))))"

  oops

text\<open>A recursive definition of evenness: \<close>
fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text\<open>A simple example of rule induction: \<close>
lemma "ev n \<longleftrightarrow> evn n"

  oops

text\<open>The power of arith: \<close>
lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
  
  oops


subsection\<open>Inductive definition of the reflexive transitive closure\<close>

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

  oops



end