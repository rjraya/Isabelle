theory Scratch
imports Complex_Main "HOL-Library.Reflection"  "HOL-Decision_Procs.Approximation"
begin

(*
To be completed
theorem assumes "3 \<le> x \<and> x \<le> 6" shows "sin ( pi / 4 ) > 0.4"
  apply(reify uneq-equations)
*)

theorem "3 \<le> x \<and> x \<le> 6 \<Longrightarrow> sin ( pi / x) > 0.4" by (approximation 10)

(*
theorem arctan1p5: "arctan 1.5 < 1"
apply(reify interpret_form.simps interpret_floatarith.simps)
apply(rule approx
apply (rule approx-inequality[where prec=10 and bs=[]])
*)

value "Float 3 (-1)"
value "approx 1 (Num (Float 3 (-2))) [Some (Float 1 0,Float 4 0)]"
value "approx 1 (Add (Num (Float 3 (-2))) (Num (Float 4 (-8)))) [Some (Float 1 0,Float 4 0)]"
value "approx 1 (Add (Var 1) (Num (Float 4 (-8)))) [Some (Float 1 0,Float 4 0)]"

(*theorem "3 \<le> x \<and> x \<le> 5 \<Longrightarrow> x \<ge> 2.4" by (approximation 10)*)

value "approx 10 (Add (Var 0) (Var 1))
         [Some (Float 1 0, Float 1 1), Some (Float (-1) 0, Float 1 1)]"

lemma "(x :: real) \<in> {1..2}  \<Longrightarrow> exp(x) \<in> {0..7.3891}"
  by (approximation 20)

lemma "(x :: real) \<in> {1..2} \<Longrightarrow> (y :: real) \<in> {3..4}  \<Longrightarrow> x/y \<in> {0..8}"
  by (approximation 20)

(* Example 8.1 Moore *) 

(*f(x) = x^2-2
X0 = [1,2]*)

(* derivative with respect to variable given by first parameter *)
value "DERIV_floatarith 1 (Var 1)"
value "DERIV_floatarith 1 (Power (Var 1) 2)" (* probably simplify 2 (x * 1) *)
value "DERIV_floatarith 1 (Cos (Var 1))" (* ? *)

definition midpoint :: "float \<Rightarrow> float \<Rightarrow> (float * float) option" where
"midpoint a b = (floor((a+b)/2),ceil((a+b)/2))"

fun newton_iteration :: "(float * float) option \<Rightarrow> 
                         (float \<Rightarrow> float) \<Rightarrow> 
                         (float * float) option" where
"newton_iteration i f = midpoint(i) - f(midpoint(i))/F'(i)"

fun newton :: "(float * float) option \<Rightarrow> 
               (float \<Rightarrow> float) \<Rightarrow> 
               nat \<Rightarrow>
               (float * float) option" where
"newton i f k = 
  (foldl ( (ai::(float * float) option) \<Rightarrow> 
           (j::nat) \<Rightarrow> 
           (newton_iteration ai f)) [1..k] i)"

term "foldl"
(*
Theorem 8.1. 

If an interval X(0) contains a zero x of f, then so does X(k) for all
k = 0,1,2,..., defined by newton. 

Furthermore, the intervals X(k) form a nested sequence  converging to x if 0 \<notin> F.
*)


end