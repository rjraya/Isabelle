theory Seminar1
  imports Main
begin

section\<open>Syntax and datatypes\<close>

subsection\<open>\<lambda>-calculus\<close>

text\<open>
  Term language based on the \<lambda>-calculus
\<close>
term "f (g x) y"
term "h (\<lambda>x. f(g x))"
term "\<lambda>x. x + x"

subsection\<open>Datatype nat\<close>

text\<open>
 At a basic level:

 datatype nat = 0 | Suc nat
 
 Recursive function definition
\<close>
 
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text\<open>
 explain how structural induction works over a datatype
 use inference rule notation
\<close>
thm nat.induct

lemma add_02: "add m 0 = m"

  oops

subsection\<open>Datatype list\<close>

datatype 'a tlist = Nil | Cons "'a" "'a tlist"

text\<open>This makes the names unqualified\<close>
declare [[names_short]]

fun app :: "'a tlist \<Rightarrow> 'a tlist \<Rightarrow> 'a tlist" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun trev :: "'a tlist \<Rightarrow> 'a tlist" where
"trev Nil = Nil" |
"trev (Cons x xs) = app (trev xs) (Cons x Nil)"

text\<open>
 Want some test cases of the above functions?
 Use "values"
\<close>

value "trev(Cons True (Cons False Nil))"

value "trev(Cons a (Cons b Nil))"

text\<open>
 Here is a theorem that requires some intuition.
\<close>

theorem rev_rev[simp]: "rev (rev xs) = xs"

  oops

subsection\<open>Datatype tree\<close>

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

text\<open>
 Recall that a datatype definition introduces three kind of theorems:
 1. Type of the constructed datatype
 2. Different constructors lead to different data
 3. Constructor with congruent arguments lead to congruent data
\<close>
lemma "Leaf \<noteq> Node l x r" by auto

text\<open>
 An example of a longer function definition.

 Write a function that given a list, interleaves a parameter a
 between its elements. For instance:
 
 x1 x2 x3 -> x1 a x2 a x3

 show its induction scheme and simplification rules.
\<close>
fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a l = undefined" 

subsection\<open>Datatype option\<close>

datatype 'a option = None | Some 'a

text\<open>
 Note the use of if (or case) in function definitions.
\<close>

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a,b) # ps) x = 
 (if a = x then Some b else lookup ps x)"

subsection\<open>Non-recursive definitions\<close>

definition sq :: "nat \<Rightarrow> nat" where "sq n = n*n"
thm sq_def
thm sq_def[of 3]
text\<open>
 Note the explicit unfolding that is required to proof
 this proposition:
\<close>
lemma "sq 3 = 9"
  
  oops

section\<open>Basic reasoning techniques\<close>

subsection\<open>Induction by generalization\<close>

text\<open>
 Often we need to generalize theorems in order to prove
 them by induction. Some heuristics can work:

 1. Replace constants by variables. 
 2. Generalize free variables (variables that are not affected
 by a quantifier)
\<close>

text\<open>
 Here itrev is an iterated version of the reverse function.
 rev is denoting the reverse function of Isabelle library, 
 to see its definition, go over the name, press control and 
 click on the name. 
\<close>
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs [] = rev xs"
apply(induction xs)
apply(auto)
  oops

subsection\<open>Computation Induction\<close>

text\<open>
 fun f :: \<tau> => \<tau>' 
 gives a special induction schema f.induct.
 To prove P(x) for every x :: \<tau>, it 
 suffices to prove, for each defining 
 equation:

 f(e) = ...f(r1)...f(rk)

 that P(e) holds assuming P(r1)...P(rk)
\<close>

fun sept :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sept a [] = []" |
"sept a [x] = [x]" |
"sept a (x#y#zs) = x # a # sept a (y#zs)"

lemma "map f (sept a xs) = sept (f a) (map f xs)"

  oops

subsection\<open>Simplification\<close>

text\<open>Simplification in conclusion\<close>
lemma "ys @ [] = []" apply(simp) oops 

text\<open>Simplification in assumption\<close>
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs" by(simp)

text\<open>Using additional rules:\<close>
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply(simp add: algebra_simps)
done

text\<open>Giving a lemma the simp-attribute:\<close>
declare algebra_simps [simp]

text\<open>Rewriting with definitions\<close>

lemma "sq(n*n) = sq(n)*sq(n)"
apply(simp add: sq_def) 
done

text\<open>Case distinctions\<close>

text\<open>Automatic:\<close>
lemma "(A & B) = (if A then B else False)" by(simp)

text\<open>Internal desugaring:\<close>
lemma "if A then B else C"
apply(simp)
oops

text{* By hand (for case): *}
lemma "1 \<le> (case ns of [] \<Rightarrow> 1 | n#_ \<Rightarrow> Suc n)"
apply(simp split: list.split)
done

text\<open>Tracing\<close>

lemma "rev[x] = []" 
using [[simp_trace]] apply(simp)
oops

text\<open>
 auto can be modified almost like simp
 instead of add use simp add
\<close>

end