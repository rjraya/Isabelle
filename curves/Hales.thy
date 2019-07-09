theory Hales
  imports Complex_Main "HOL-Algebra.Group" "HOL-Algebra.Bij"
begin

section\<open>Edwards curves\<close>

locale curve_addition =
  fixes c d :: real
begin      

definition e :: "real \<Rightarrow> real \<Rightarrow> real" where
 "e x y = x^2 + c * y^2 - 1 - d * x^2 * y^2"

definition delta_plus :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

definition delta_minus :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

definition delta :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * 
                      (delta_minus x1 y1 x2 y2)"

fun add :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real" where
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - c*y1*y2) div (1-d*x1*y1*x2*y2), 
     (x1*y2+y1*x2) div (1+d*x1*y1*x2*y2))"

lemma add_with_deltas:
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2), 
     (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2))"
  unfolding delta_minus_def delta_plus_def
  by(simp add: algebra_simps)

lemma commutativity: "add z1 z2 = add z2 z1"
  by(cases "z1",cases "z2",simp add: algebra_simps)

(* try first with integers, in paper they use general rings *)

lemma closure: 
  assumes "z1 = (x1,y1)" "z2 = (x2,y2)" "z3 = (x3,y3)" "z3 = add z1 z2"
  assumes "delta_minus x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0"
  assumes "e x1 y1 == 0" "e x2 y2 == 0" 
  shows "e x3 y3 == 0" 
proof -
  have x3_expr: "x3 = (x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2)"
    using assms add_with_deltas by auto
  have y3_expr: "y3 = (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2)"
    using assms add_with_deltas by auto
  define prod where "prod = 
    -1 + x1^2 * x2^2 + c * x2^2 * y1^2 - d * x1^2 * x2^4 * y1^2 + 
     c * x1^2 * y2^2 - d * x1^4 * x2^2 * y2^2 + c^2 * y1^2 * y2^2 - 
     4 * c * d * x1^2 * x2^2 * y1^2 * y2^2 + 
     2 * d^2 * x1^2 * x2^2 * y1^2 * y2^2 + d^2 * x1^4 * x2^4 * y1^2 * y2^2 - 
     c^2 * d * x2^2 * y1^4 * y2^2 + c * d^2 * x1^2 * x2^4 * y1^4 * y2^2 - 
     c^2 * d * x1^2 * y1^2 * y2^4 + c * d^2 * x1^4 * x2^2 * y1^2 * y2^4 + 
     c^2 * d^2 * x1^2 * x2^2 * y1^4 * y2^4 - 
     d^4 * x1^4 * x2^4 * y1^4 * y2^4"    
  define r1 where "r1 =
    x2^4 + 4 * c * x2^2 * y2^2 - 2 * d * x2^2 * y2^2 - 
    2 * c * x2^4 * y2^2 - d * x1^2 * x2^4 * y2^2 - 
    c * d * x2^4 * y1^2 * y2^2 + c^2 * y2^4 - 2 * c^2 * x2^2 * y2^4 - 
    c * d * x1^2 * x2^2 * y2^4 + 2 * c * d * x2^4 * y2^4 - 
    d^2 * x2^4 * y2^4 + d^2 * x1^2 * x2^4 * y2^4 - 
    c^2 * d * x2^2 * y1^2 * y2^4 + c * d^2 * x2^4 * y1^2 * y2^4 + 
    d^3 * x1^2 * x2^4 * y1^2 * y2^4
  "
  define r2 where "r2 = 
    1 + x2^2 - x1^2 * x2^2 - c * x2^2 * y1^2 + c * y2^2 - 
    c * x1^2 * y2^2 - 2 * c * x2^2 * y2^2 + d * x2^2 * y2^2 + 
    2 * c * x1^2 * x2^2 * y2^2 - 2 * d * x1^2 * x2^2 * y2^2 + 
    d * x1^4 * x2^2 * y2^2 - c^2 * y1^2 * y2^2 + 
    2 * c^2 * x2^2 * y1^2 * y2^2 - 2 * c * d * x2^2 * y1^2 * y2^2 + 
    c^2 * d * x2^2 * y1^4 * y2^2
  "

  define e1 where "e1 = e x1 y1"
  define e2 where "e2 = e x2 y2"
  have prod_eq_1: "prod - (r1 * e1 + r2 * e2) = 0"
    unfolding prod_def r1_def e1_def r2_def e2_def e_def              
    by(simp add: algebra_simps,algebra) 

  define a where "a = x1*x2 - c*y1*y2"
  define b where "b = x1*y2+y1*x2"

  have "(e x3 y3)*(delta x1 y1 x2 y2)\<^sup>2 =
         e (a div (delta_minus x1 y1 x2 y2))
           (b div (delta_plus x1 y1 x2 y2)) * (delta x1 y1 x2 y2)\<^sup>2"
    unfolding a_def b_def
    by (simp add: assms(3) mult.commute mult.left_commute x3_expr y3_expr)
  also have "... = 
    ((a div delta_minus x1 y1 x2 y2)\<^sup>2 +
    c * (b div delta_plus x1 y1 x2 y2)\<^sup>2 -
    1 -
    d * (a div delta_minus x1 y1 x2 y2)\<^sup>2 *
   (b div delta_plus x1 y1 x2 y2)\<^sup>2) * (delta x1 y1 x2 y2)\<^sup>2"
    unfolding delta_plus_def delta_minus_def delta_def e_def
    by simp
  also have "... = 
    ((a div delta_minus x1 y1 x2 y2)\<^sup>2 * (delta x1 y1 x2 y2)\<^sup>2 +
    c * (b div delta_plus x1 y1 x2 y2)\<^sup>2 * (delta x1 y1 x2 y2)\<^sup>2 -
    1 * (delta x1 y1 x2 y2)\<^sup>2 -
    d * (a div delta_minus x1 y1 x2 y2)\<^sup>2 *
   (b div delta_plus x1 y1 x2 y2)\<^sup>2 * (delta x1 y1 x2 y2)\<^sup>2)"
    by(simp add: algebra_simps)
  also have "... = 
    ((a * delta_plus x1 y1 x2 y2)\<^sup>2 +
    c * (b * delta_minus x1 y1 x2 y2)\<^sup>2 -
    (delta x1 y1 x2 y2)\<^sup>2 -
    d * a\<^sup>2 * b\<^sup>2)"
   unfolding delta_def by(simp add: field_simps assms(5,6))+
  also have "... - prod = 0"
    unfolding prod_def delta_plus_def 
              delta_minus_def delta_def
              a_def b_def
    by algebra
  finally have "(e x3 y3)*(delta x1 y1 x2 y2)\<^sup>2 = prod"
    by simp
  then have prod_eq_2: "(e x3 y3) = prod div (delta x1 y1 x2 y2)\<^sup>2"
    using assms(5,6) delta_def by auto

  have "e1 == 0" unfolding e1_def using assms(7) by simp
  moreover have "e2 == 0" unfolding e2_def using assms(8) by simp
  ultimately have "prod == 0" 
    using prod_eq_1 by simp
  then show "e x3 y3 == 0" using prod_eq_2 by simp
qed

lemma associativity: 
  assumes "z1 = (x1,y1)" "z2 = (x2,y2)" "z3 = (x3,y3)"
          "z1' = (x1',y1')" "z3' = (x3',y3')"
  assumes "z1' = add z1 z2" "z3' = add z2 z3"
  assumes "delta_minus x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0"
          "delta_minus x2 y2 x3 y3 \<noteq> 0" "delta_plus x2 y2 x3 y3 \<noteq> 0"
          "delta_minus x1' y1' x3 y3 \<noteq> 0" "delta_plus x1' y1' x3 y3 \<noteq> 0"
          "delta_minus x1 y1 x3' y3' \<noteq> 0" "delta_plus x1 y1 x3' y3' \<noteq> 0"
  assumes "e x1 y1 == 0" "e x2 y2 == 0" "e x3 y3 == 0" 
  shows "add (add z1 z2) z3 = add z1 (add z2 z3)" 
proof -
 define e1 where "e1 = e x1 y1"
 define e2 where "e2 = e x2 y2"
 define e3 where "e3 = e x3 y3"
 define Delta\<^sub>x where "Delta\<^sub>x = 
   (delta_minus x1' y1' x3 y3)*(delta_minus x1 y1 x3' y3')*
   (delta x1 y1 x2 y2)*(delta x2 y2 x3 y3)" 
 define Delta\<^sub>y where "Delta\<^sub>y =
   (delta_plus x1' y1' x3 y3)*(delta_plus x1 y1 x3' y3')*
   (delta x1 y1 x2 y2)*(delta x2 y2 x3 y3)" 
 define g\<^sub>x :: real where "g\<^sub>x = fst(add z1' z3) - fst(add z1 z3')"
 define g\<^sub>y where "g\<^sub>y = snd(add z1' z3) - snd(add z1 z3')"
 define gxpoly where "gxpoly = g\<^sub>x * Delta\<^sub>x"
 define gypoly where "gypoly = g\<^sub>y * Delta\<^sub>y"
 
 define r1x where "r1x = 
    -d*x1*x2^3*x3*y2^2+d*x1*x2^3*x3^3*y2^2+c*d*x2^2*x3*y1*y2^3-c*d*x2^2*x3^3*y1*y2^3
    +d*x1*x2^4*x3^2*y2*y3+c*d*x2^3*y1*y2^2*y3+c*d*x1*x2^2*y2^3*y3-d^2*x1*x2^4*x3^2*y2^3*y3
    +c^2*d*x2*x3^2*y1*y2^4*y3-c*d^2*x2^3*x3^2*y1*y2^4*y3+c*d*x2^4*x3*y1*y2*y3^2
    -c*d^2*x2^4*x3*y1*y2^3*y3^2-c^2*d*x1*x2*x3*y2^4*y3^2+c*d^2*x1*x2^3*x3*y2^4*y3^2
    -c^2*d*x2^3*y1*y2^2*y3^3-c^2*d*x1*x2^2*y2^3*y3^3"
 define r2x where "r2x = 
    x1*x2*x3-x1^3*x2*x3-x1*x2*x3^3+x1^3*x2*x3^3-c*x1*x2*x3*y1^2+c*x1*x2*x3^3*y1^2
    -c*x3*y1*y2+c*x1^2*x3*y1*y2+c*x3^3*y1*y2-c*x1^2*x3^3*y1*y2+c^2*x3*y1^3*y2-c^2*x3^3*y1^3*y2
    -c*x2*y1*y3+c*x1^2*x2*y1*y3+c*x2*x3^2*y1*y3-c*x1^2*x2*x3^2*y1* y3+c^2*x2*y1^3*y3-c^2*x2*x3^2*y1^3*y3
    -c*x1*y2*y3+c*x1^3*y2*y3+c*x1*x3^2*y2*y3-c* x1^3*x3^2*y2*y3+d*x1*x2^2*x3^2*y2*y3-d*x1^3*x2^2*x3^2*y2*y3
    +c^2*x1*y1^2*y2*y3-c^2*x1*x3^2*y1^2*y2*y3-c*d*x1*x2^2*x3^2*y1^2*y2*y3+c*d*x2*x3^2*y1*y2^2*y3
    -c*d*x1^2*x2*x3^2*y1*y2^2*y3-c^2*d*x2*x3^2*y1^3*y2^2*y3-c*x1*x2*x3*y3^2+c*x1^3*x2*x3*y3^2
    +d*x1*x2*x3^3*y3^2-d*x1^3*x2*x3^3*y3^2+c^2*x1*x2*x3*y1^2*y3^2-c*d*x1*x2*x3^3*y1^2*y3^2+c^2*x3*y1*y2*y3^2
    -c^2*x1^2*x3*y1*y2*y3^2+c*d*x2^2*x3*y1*y2*y3^2-c*d*x1^2*x2^2*x3*y1*y2*y3^2-c*d*x3^3*y1*y2*y3^2
    +c*d*x1^2*x3^3*y1*y2*y3^2+d^2*x1^2*x2^2*x3^3*y1*y2*y3^2-c^3*x3*y1^3*y2*y3^2-c^2*d*x2^2*x3*y1^3*y2*y3^2
    +c^2*d*x3^3*y1^3*y2*y3^2-c*d*x1*x2*x3*y2^2*y3^2+c*d*x1^3*x2*x3*y2^2*y3^2+c^2*d*x1*x2*x3*y1^2*y2^2*y3^2
    -c* d^2*x1*x2*x3^3*y1^2*y2^2*y3^2+c^2*x2*y1*y3^3-c^2*x1^2*x2*y1*y3^3-c*d*x2*x3^2*y1*y3^3+c*d*x1^2*x2*x3^2*y1*y3^3
    -c^3*x2*y1^3*y3^3+c^2*d*x2*x3^2*y1^3*y3^3+c^2*x1*y2*y3^3-c^2*x1^3*y2*y3^3-c*d*x1*x3^2*y2*y3^3
    +c*d*x1^3*x3^2*y2*y3^3-c^3*x1*y1^2*y2*y3^3+c^2*d*x1*x3^2*y1^2*y2*y3^3+c*d^2*x1*x2^2*x3^2*y1^2*y2*y3^3
    +c* d^2*x1^2*x2*x3^2*y1*y2^2*y3^3"
  define r3x where "r3x = 
    -x1*x2*x3+x1^3*x2*x3+x1*x2^3*x3-x1^3*x2^3*x3+c*x1*x2*x3*y1^2-c*x1*x2^3*x3*y1^2+c*x3*y1*y2
    -c*x1^2*x3*y1*y2-c*x2^2*x3*y1*y2+c*x1^2*x2^2*x3*y1*y2-d*x1^2*x2^2*x3*y1*y2-c^2*x3*y1^3*y2
    +c^2*x2^2*x3*y1^3*y2+c*x1*x2*x3*y2^2-c*x1^3*x2*x3*y2^2-c^2*x1*x2*x3*y1^2*y2^2+c*d*x1*x2*x3*y1^2*y2^2
    -c^2*x3*y1*y2^3+c^2*x1^2*x3*y1*y2^3+c^3*x3*y1^3*y2^3+c*x2*y1*y3-c*x1^2*x2*y1*y3-c*x2^3*y1*y3
    +c*x1^2*x2^3*y1*y3-c^2*x2*y1^3*y3+c^2*x2^3*y1^3*y3+c*x1*y2*y3-c*x1^3*y2*y3-c*x1*x2^2*y2*y3
    +c*x1^3*x2^2*y2*y3-c^2*x1*y1^2*y2*y3+c^2*x1*x2^2*y1^2*y2*y3-c*d*x1*x2^2*y1^2*y2*y3-c^2*x2*y1*y2^2*y3
    +c^2*x1^2*x2*y1*y2^2*y3-c*d*x1^2*x2*y1*y2^2*y3+c^3*x2*y1^3*y2^2*y3-c^2*x1*y2^3*y3+c^2*x1^3*y2^3*y3
    +c^3*x1*y1^2*y2^3*y3"
  
  define r1y where "r1y = 
    -d*x2^3*x3*y1*y2^2+d*x2^3*x3^3*y1*y2^2-d*x1*x2^2*x3*y2^3+d*x1*x2^2*x3^3*y2^3+d*x2^4*x3^2*y1*y2*y3
    -d*x1*x2^3*y2^2*y3+c*d*x2^2*y1*y2^3*y3-d^2*x2^4*x3^2*y1*y2^3*y3-c*d*x1*x2*x3^2*y2^4*y3+d^2*x1*x2^3*x3^2*y2^4*y3
    -d*x1*x2^4*x3*y2*y3^2+d^2*x1*x2^4* x3*y2^3*y3^2-c^2*d*x2*x3*y1*y2^4*y3^2+c*d^2*x2^3*x3*y1*y2^4*y3^2
    +c*d*x1*x2^3*y2^2* y3^3-c^2*d*x2^2*y1*y2^3*y3^3"
  define r2y where "r2y = 
    x2*x3*y1-x1^2*x2*x3*y1-x2*x3^3*y1+x1^2*x2*x3^3*y1-c*x2*x3*y1^3+c*x2*x3^3*y1^3+x1*x3*y2-x1^3*x3*y2
    -x1*x3^3*y2+x1^3*x3^3*y2-c*x1*x3*y1^2*y2+c*x1*x3^3*y1^2*y2+x1*x2*y3-x1^3*x2*y3-x1*x2*x3^2*y3
    +x1^3*x2*x3^2*y3-c*x1*x2*y1^2*y3+c*x1*x2*x3^2*y1^2*y3-c*y1*y2*y3+c*x1^2*y1*y2*y3+c*x3^2*y1*y2*y3
    -c*x1^2*x3^2*y1*y2*y3+d*x2^2*x3^2*y1*y2*y3-d*x1^2*x2^2*x3^2*y1*y2*y3+c^2*y1^3*y2*y3-c^2*x3^2*y1^3*y2*y3
    -c*d*x2^2*x3^2*y1^3*y2*y3-d*x1*x2*x3^2*y2^2*y3+d*x1^3*x2*x3^2*y2^2*y3+c*d*x1*x2*x3^2*y1^2*y2^2*y3
    -c*x2*x3*y1*y3^2+c*x1^2*x2*x3*y1*y3^2+d*x2*x3^3*y1*y3^2-d*x1^2*x2*x3^3*y1*y3^2+c^2*x2*x3*y1^3*y3^2
    -c*d*x2*x3^3*y1^3*y3^2-c*x1*x3*y2*y3^2+c*x1^3*x3*y2*y3^2-d*x1*x2^2*x3*y2*y3^2+d*x1^3*x2^2*x3*y2*y3^2
    +d*x1*x3^3*y2*y3^2-d*x1^3*x3^3*y2*y3^2+c^2*x1*x3*y1^2*y2*y3^2+c*d*x1*x2^2*x3*y1^2*y2*y3^2
    -c*d*x1*x3^3*y1^2*y2*y3^2-d^2*x1*x2^2*x3^3*y1^2*y2*y3^2-c*d*x2*x3*y1*y2^2*y3^2+c*d*x1^2*x2*x3*y1*y2^2*y3^2
    -d^2*x1^2*x2*x3^3*y1*y2^2*y3^2+c^2*d*x2*x3*y1^3*y2^2*y3^2-c*x1*x2*y3^3+c*x1^3*x2*y3^3+d*x1*x2*x3^2*y3^3
    -d*x1^3*x2*x3^2*y3^3+c^2*x1*x2*y1^2*y3^3-c*d*x1*x2*x3^2*y1^2*y3^3+c^2*y1*y2*y3^3-c^2*x1^2*y1*y2*y3^3
    -c*d*x3^2*y1*y2*y3^3+c*d*x1^2*x3^2*y1*y2*y3^3+d^2*x1^2*x2^2*x3^2*y1*y2*y3^3-c^3*y1^3*y2*y3^3
    +c^2*d*x3^2*y1^3*y2*y3^3-c*d^2*x1*x2*x3^2*y1^2*y2^2*y3^3"
  define r3y where "r3y = 
    -x2*x3*y1+x1^2*x2*x3*y1+x2^3*x3*y1-x1^2*x2^3*x3*y1+c*x2*x3*y1^3-c*x2^3*x3*y1^3-x1*x3*y2+x1^3*x3*y2+
    x1*x2^2*x3*y2-x1^3*x2^2*x3*y2+c*x1*x3*y1^2*y2-c*x1*x2^2*x3*y1^2*y2+d*x1*x2^2*x3*y1^2*y2+c*x2*x3*y1*y2^2
    -c*x1^2*x2*x3*y1*y2^2+d*x1^2*x2*x3*y1*y2^2-c^2*x2*x3*y1^3*y2^2+c*x1*x3*y2^3-c*x1^3*x3*y2^3-c^2*x1*x3*y1^2*y2^3
    -x1*x2*y3+x1^3*x2*y3+x1*x2^3*y3-x1^3*x2^3*y3+c*x1*x2*y1^2*y3-c*x1*x2^3*y1^2*y3+c*y1*y2*y3-c*x1^2*y1*y2*y3
    -c*x2^2*y1*y2*y3+c*x1^2*x2^2*y1*y2*y3-d*x1^2*x2^2*y1*y2*y3-c^2*y1^3*y2*y3+c^2*x2^2*y1^3*y2*y3+c*x1*x2*y2^2*y3
    -c*x1^3*x2*y2^2*y3-c^2*x1*x2*y1^2*y2^2*y3+c*d*x1*x2*y1^2*y2^2*y3-c^2*y1*y2^3*y3+c^2*x1^2*y1*y2^3*y3
    +c^3*y1^3*y2^3*y3"
  define gxpoly_expr where "gxpoly_expr = 
    d*x2* y2* (x1^2* x2* x3* y1-x1^2* x2* x3^3* y1-c* x1* x3* y1^2* y2+d* x1^3* x2^2* x3* y1^2* y2
    +c* x1* x3^3* y1^2* y2-d* x1^3* x2^2* x3^3* y1^2* y2-c* d* x1^2* x2* x3* y1^3* y2^2+c* d* x1^2* x2* x3^3* y1^3* y2^2
    -x1* x2* x3^2* y3+x1^3* x2* x3^2* y3+c* x1* x2* y1^2* y3-d* x1^3* x2^3* x3^2* y1^2* y3+c* x1^2* y1* y2* y3
    -c* x3^2* y1* y2* y3-c* d* x1^2* x2^2* y1^3* y2* y3+c^2* x3^2* y1^3* y2* y3-c* d* x1^3* x2* y1^2* y2^2* y3
    +d^2* x1^3* x2^3* x3^2* y1^2* y2^2* y3-c^2* d* x1^2* x3^2* y1^3* y2^3* y3+c* d^2* x1^2* x2^2* x3^2* y1^3* y2^3* y3
    -c* x2* x3* y1* y3^2+d* x1^2* x2^3* x3^3* y1* y3^2+c^2* x2* x3* y1^3* y3^2-c* d* x1^2* x2^3* x3* y1^3* y3^2
    +c* x1* x3* y2* y3^2-c* x1^3* x3* y2* y3^2-d* x1* x2^2* x3^3* y2* y3^2+d* x1^3* x2^2* x3^3* y2* y3^2
    +c* d* x2* x3^3* y1* y2^2* y3^2-d^2* x1^2* x2^3* x3^3* y1* y2^2* y3^2+c* d^2* x1^2* x2^3* x3* y1^3* y2^2* y3^2
    -c^2* d *x2* x3^3* y1^3* y2^2* y3^2+c^2* d* x1^3* x3* y1^2* y2^3* y3^2-c* d^2* x1^3 *x2^2* x3* y1^2* y2^3* y3^2
    -c^2* d* x1* x3^3* y1^2* y2^3* y3^2+c* d^2* x1* x2^2* x3^3* y1^2* y2^3* y3^2-c^2* x1* x2* y1^2* y3^3
    +c* d* x1* x2^3* x3^2* y1^2* y3^3-c^2* x1^2* y1* y2* y3^3+c* d* x2^2* x3^2* y1* y2* y3^3+c^2* d* x1^2* x2^2* y1^3* y2* y3^3
    -c^2* d* x2^2* x3^2* y1^3* y2* y3^3+c* d* x1* x2* x3^2* y2^2* y3^3-c* d *x1^3* x2* x3^2* y2^2* y3^3
    +c^2* d* x1^3* x2* y1^2* y2^2* y3^3-c* d^2* x1* x2^3* x3^2* y1^2* y2^2* y3^3+c^2* d* x1^2* x3^2* y1* y2^3* y3^3
    -c* d^2* x1^2* x2^2* x3^2* y1* y2^3* y3^3)"

  define gypoly_expr where "gypoly_expr = 
   -d* x2* y2* (x1* x2* x3* y1^2-x1* x2* x3^3* y1^2+x1^2* x3* y1* y2-x1^2* x3^3* y1* y2-d* x1^2* x2^2* x3* y1^3* y2
   +d* x1^2* x2^2* x3^3* y1^3* y2-d* x1^3* x2* x3* y1^2* y2^2+d* x1^3* x2* x3^3* y1^2 *y2^2-x1^2* x2* y1* y3
   +x2* x3^2* y1* y3-c* x2* x3^2* y1^3* y3+d* x1^2* x2^3* x3^2* y1^3* y3-x1* x3^2* y2* y3+x1^3* x3^2* y2* y3
   +c* x1* y1^2* y2* y3-d* x1^3* x2^2* y1^2* y2* y3+c* d* x1^2* x2* y1^3* y2^2* y3-d^2* x1^2* x2^3* x3^2* y1^3* y2^2* y3
   -c* d* x1^3* x3^2* y1^2* y2^3* y3+d^2* x1^3* x2^2* x3^2* y1^2* y2^3* y3-x1* x2* x3* y3^2+x1^3* x2* x3* y3^2
   -d* x1^3* x2^3* x3* y1^2* y3^2+d* x1* x2^3* x3^3* y1^2* y3^2-c* x3* y1* y2* y3^2+d *x2^2* x3^3* y1* y2* y3^2
   +c^2* x3* y1^3* y2* y3^2-c* d* x2^2* x3^3* y1^3* y2 *y3^2+d* x1* x2* x3^3* y2^2* y3^2-d* x1^3* x2* x3^3* y2^2* y3^2
   +d^2* x1^3* x2^3* x3 *y1^2* y2^2* y3^2-d^2* x1* x2^3* x3^3* y1^2* y2^2* y3^2+c* d* x1^2* x3^3* y1* y2^3* y3^2
   -d^2* x1^2* x2^2* x3^3* y1* y2^3* y3^2-c^2* d* x1^2* x3* y1^3* y2^3* y3^2+c* d^2* x1^2* x2^2* x3* y1^3* y2^3* y3^2
   +c* x1^2* x2* y1* y3^3-d* x1^2* x2^3* x3^2* y1* y3^3+d* x1* x2^2* x3^2* y2* y3^3-d* x1^3* x2^2* x3^2* y2* y3^3
   -c^2* x1* y1^2 *y2* y3^3+c* d *x1^3* x2^2* y1^2* y2* y3^3-c* d* x2* x3^2* y1* y2^2* y3^3+d^2* x1^2* x2^3* x3^2* y1* y2^2* y3^3
   -c^2* d* x1^2* x2* y1^3* y2^2* y3^3+c^2* d* x2* x3^2* y1^3* y2^2* y3^3+c^2* d* x1* x3^2* y1^2* y2^3* y3^3
   -c* d^2* x1* x2^2* x3^2* y1^2* y2^3* y3^3)"

  have x1'_expr: "x1' = (x1 * x2 - c * y1 * y2) / (1 - d * x1 * y1 * x2 * y2)"
    using assms(1,2,4,6) by auto
  have y1'_expr: "y1' = (x1 * y2 + y1 * x2) / (1 + d * x1 * y1 * x2 * y2)"
    using assms(1,2,4,6) by auto
  have x3'_expr: "x3' = (x2 * x3 - c * y2 * y3) / (1 - d * x2 * y2 * x3 * y3)"
    using assms(2,3,5,7) by auto
  have y3'_expr: "y3' = (x2 * y3 + y2 * x3) / (1 + d * x2 * y2 * x3 * y3)"
    using assms(2,3,5,7) by auto
  
  have non_unfolded_adds:
      "delta x1 y1 x2 y2 \<noteq> 0" 
    using delta_def assms(8,9) by auto

  have unfolded_adds:
       "1 - d * x1 * y1 * x2 * y2 \<noteq> 0"
       "1 + d * x1 * y1 * x2 * y2 \<noteq> 0"
       "1 - d * x2 * y2 * x3 * y3 \<noteq> 0"
       "1 + d * x2 * y2 * x3 * y3 \<noteq> 0"
       "1 - d * x1' * y1' * x3 * y3 \<noteq> 0"
       "1 + d * x1' * y1' * x3 * y3 \<noteq> 0"
       "1 - d * x1 * y1 * x3' * y3' \<noteq> 0"
       "1 + d * x1 * y1 * x3' * y3' \<noteq> 0"
    using assms(8-15)
    unfolding delta_plus_def delta_minus_def by blast+
  
  have "gxpoly_expr = r1x * e1 + r2x * e2 + r3x * e3"
    unfolding gxpoly_expr_def r1x_def e1_def r2x_def e2_def r3x_def e3_def e_def             
    by algebra

  have simp1gx: "
    (x1' * x3 - c * y1' * y3) * local.delta_minus x1 y1 x3' y3' *
    (local.delta x1 y1 x2 y2 * local.delta x2 y2 x3 y3) = 
    ((x1 * x2 - c * y1 * y2) * x3 * local.delta_plus x1 y1 x2 y2 -
     c * (x1 * y2 + y1 * x2) * y3 * local.delta_minus x1 y1 x2 y2) *
    (local.delta_minus x2 y2 x3 y3 * local.delta_plus x2 y2 x3 y3 -
     d * x1 * y1 * (x2 * x3 - c * y2 * y3) * (x2 * y3 + y2 * x3))
  "
    apply((subst x1'_expr)+, (subst y1'_expr)+,(subst x3'_expr)+,(subst y3'_expr)+)
    apply((subst delta_minus_def[symmetric])+,(subst delta_plus_def[symmetric])+)
    apply(subst (3) delta_minus_def)
    unfolding delta_def
    by(simp add: divide_simps assms(8-15))

  have simp2gx:
    "(x1 * x3' - c * y1 * y3') * local.delta_minus x1' y1' x3 y3 *
    (local.delta x1 y1 x2 y2 * local.delta x2 y2 x3 y3) = 
    (x1 * (x2 * x3 - c * y2 * y3) * local.delta_plus x2 y2 x3 y3 -
     c * y1 * (x2 * y3 + y2 * x3) * local.delta_minus x2 y2 x3 y3) *
    (local.delta_minus x1 y1 x2 y2 * local.delta_plus x1 y1 x2 y2 -
     d * (x1 * x2 - c * y1 * y2) * (x1 * y2 + y1 * x2) * x3 * y3)"
    apply((subst x1'_expr)+, (subst y1'_expr)+,(subst x3'_expr)+,(subst y3'_expr)+)
    apply((subst delta_minus_def[symmetric])+,(subst delta_plus_def[symmetric])+)
    apply(subst (3) delta_minus_def)
    unfolding delta_def
    by(simp add: divide_simps assms(8-15))

  have "gxpoly = gxpoly_expr"
    unfolding gxpoly_def g\<^sub>x_def Delta\<^sub>x_def 
    apply(simp add: assms(1,3,4,5))
    apply(subst delta_minus_def[symmetric])+
    apply(simp add: divide_simps assms(8-15))
    apply(subst (3) left_diff_distrib)
    apply(simp add: simp1gx simp2gx)
    unfolding delta_minus_def delta_plus_def (* equality *)
    unfolding gxpoly_expr_def
    by algebra

  have "gxpoly = r1x * e1 + r2x * e2 + r3x * e3"
    using \<open>gxpoly = gxpoly_expr\<close> \<open>gxpoly_expr = r1x * e1 + r2x * e2 + r3x * e3\<close> by auto
  then have "gxpoly = 0" 
    using e1_def assms(16) e2_def assms(17) e3_def assms(18) by auto
  have "Delta\<^sub>x \<noteq> 0" 
    using Delta\<^sub>x_def delta_def assms(10-14) non_unfolded_adds by auto
  then have "g\<^sub>x = 0" 
    using \<open>gxpoly = 0\<close> gxpoly_def by auto

  have "gypoly_expr = r1y * e1 + r2y * e2 + r3y * e3"
    unfolding gypoly_expr_def r1y_def e1_def r2y_def e2_def r3y_def e3_def e_def             
    by algebra

  have simp1gy: "(x1' * y3 + y1' * x3) * local.delta_plus x1 y1 x3' y3' *
    (local.delta x1 y1 x2 y2 * local.delta x2 y2 x3 y3) = 
    ((x1 * x2 - c * y1 * y2) * y3 * local.delta_plus x1 y1 x2 y2 +
     (x1 * y2 + y1 * x2) * x3 * local.delta_minus x1 y1 x2 y2) *
    (local.delta_minus x2 y2 x3 y3 * local.delta_plus x2 y2 x3 y3 +
     d * x1 * y1 * (x2 * x3 - c * y2 * y3) * (x2 * y3 + y2 * x3))"
    apply((subst x1'_expr)+, (subst y1'_expr)+,(subst x3'_expr)+,(subst y3'_expr)+)
    apply((subst delta_minus_def[symmetric])+,(subst delta_plus_def[symmetric])+)
    apply(subst (2) delta_plus_def)
    unfolding delta_def
    by(simp add: divide_simps assms(8-15))

  have simp2gy: "(x1 * y3' + y1 * x3') * local.delta_plus x1' y1' x3 y3 *
    (local.delta x1 y1 x2 y2 * local.delta x2 y2 x3 y3) = 
     (x1 * (x2 * y3 + y2 * x3) * local.delta_minus x2 y2 x3 y3 +
     y1 * (x2 * x3 - c * y2 * y3) * local.delta_plus x2 y2 x3 y3) *
    (local.delta_minus x1 y1 x2 y2 * local.delta_plus x1 y1 x2 y2 +
     d * (x1 * x2 - c * y1 * y2) * (x1 * y2 + y1 * x2) * x3 * y3)"
    apply((subst x1'_expr)+, (subst y1'_expr)+,(subst x3'_expr)+,(subst y3'_expr)+)
    apply((subst delta_minus_def[symmetric])+,(subst delta_plus_def[symmetric])+)
    apply(subst (3) delta_plus_def)
    unfolding delta_def
    by(simp add: divide_simps assms(8-15))

  have "gypoly = gypoly_expr"
    unfolding gypoly_def g\<^sub>y_def Delta\<^sub>y_def 
    apply(simp add: assms(1,3,4,5))
    apply(subst delta_plus_def[symmetric])+
    apply(simp add: divide_simps assms(8-15))
    apply(subst left_diff_distrib)
    apply(simp add: simp1gy simp2gy)
    unfolding delta_minus_def delta_plus_def (* equality *)
    unfolding gypoly_expr_def
    by algebra

  have "gypoly = r1y * e1 + r2y * e2 + r3y * e3"
    using \<open>gypoly = gypoly_expr\<close> \<open>gypoly_expr = r1y * e1 + r2y * e2 + r3y * e3\<close> by auto
  then have "gypoly = 0" 
    using e1_def assms(16) e2_def assms(17) e3_def assms(18) by auto
  have "Delta\<^sub>y \<noteq> 0" 
    using Delta\<^sub>y_def delta_def assms(10-15) non_unfolded_adds by auto
  then have "g\<^sub>y = 0" 
    using \<open>gypoly = 0\<close> gypoly_def by auto

  show ?thesis 
    using \<open>g\<^sub>y = 0\<close> \<open>g\<^sub>x = 0\<close> 
    unfolding g\<^sub>x_def g\<^sub>y_def assms(6) assms(7) 
    by (simp add: prod_eq_iff)
qed

lemma neutral: "add z (1,0) = z" by(cases "z",simp)

lemma inverse:
  assumes "e a b == 0" "delta a b a b \<noteq> 0" 
  shows "add (a,b) (a,-b) = (1,0)" 
  using assms
  apply(simp,subst delta_plus_def[symmetric])+
  apply(rule conjI)
  using delta_def apply simp
  unfolding e_def delta_plus_def
  by (smt mult.assoc power2_eq_square semiring_normalization_rules(16))

lemma affine_closure:
  assumes "delta x1 y1 x2 y2 = 0" "e x1 y1 = 0" "e x2 y2 = 0"
  shows "\<exists> b. (1/d = b^2 \<and> 1/d \<noteq> 0) \<or> (1/(c*d) = b^2 \<and> 1/(c*d) \<noteq> 0)" 
proof -
  define r where "r = (1 - c*d*y1^2*y2^2) * (1 - d*y1^2*x2^2)" 
  define e1 where "e1 = e x1 y1"
  define e2 where "e2 = e x2 y2"
  have "r = d^2 * y1^2 * y2^2 * x2^2 * e1 + (1 - d * y1^2) * delta x1 y1 x2 y2 - d * y1^2 * e2"
    unfolding r_def e1_def e2_def delta_def delta_plus_def delta_minus_def e_def
    by algebra
  then have "r = 0" 
    using assms e1_def e2_def by simp
  then have cases: "(1 - c*d*y1^2*y2^2) = 0 \<or> (1 - d*y1^2*x2^2) = 0" 
    using r_def by auto
  have "d \<noteq> 0" using \<open>r = 0\<close> r_def by auto
  {assume "(1 - d*y1^2*x2^2) = 0"
  then have "1/d = y1^2*x2^2" "1/d \<noteq> 0"
    by(auto simp add: divide_simps \<open>d \<noteq> 0\<close>,argo)}
  note case1 = this
  {assume "(1 - c*d*y1^2*y2^2) = 0" "(1 - d*y1^2*x2^2) \<noteq> 0"
    then have "c \<noteq> 0" by auto
    then have "1/(c*d) = y1^2*y2^2" "1/(c*d) \<noteq> 0" 
      apply(simp add: divide_simps \<open>d \<noteq> 0\<close> \<open>c \<noteq> 0\<close>) 
      using \<open>(1 - c*d*y1^2*y2^2) = 0\<close> apply argo
      using \<open>c \<noteq> 0\<close> \<open>d \<noteq> 0\<close> by auto
  }
  note case2 = this
  
  show "\<exists> b. (1/d = b^2 \<and> 1/d \<noteq> 0) \<or> (1/(c*d) = b^2 \<and> 1/(c*d) \<noteq> 0)" 
    using cases case1 case2 by (metis power_mult_distrib)
qed

lemma delta_non_zero:
  fixes x1 y1 x2 y2
  assumes "e x1 y1 = 0" "e x2 y2 = 0"
  assumes "\<exists> b. 1/c = b^2" "\<not> (\<exists> b. b \<noteq> 0 \<and> 1/d = b^2)"
  shows "delta x1 y1 x2 y2 \<noteq> 0"
proof(rule ccontr)
  assume "\<not> delta x1 y1 x2 y2 \<noteq> 0"
  then have "delta x1 y1 x2 y2 = 0" by blast
  then have "\<exists> b. (1/d = b^2 \<and> 1/d \<noteq> 0) \<or> (1/(c*d) = b^2 \<and> 1/(c*d) \<noteq> 0)" 
   using affine_closure[OF \<open>delta x1 y1 x2 y2 = 0\<close> 
                            \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close>] by blast
  then obtain b where "(1/(c*d) = b^2 \<and> 1/(c*d) \<noteq> 0)"
   using \<open>\<not> (\<exists> b. b \<noteq> 0 \<and> 1/d = b^2)\<close> by fastforce
  then have "1/c \<noteq> 0" "c \<noteq> 0" "d \<noteq> 0" "1/d \<noteq> 0" by simp+
  then have "1/d = b^2 / (1/c)"
   apply(simp add: divide_simps)
   by (metis \<open>1 / (c * d) = b\<^sup>2 \<and> 1 / (c * d) \<noteq> 0\<close> eq_divide_eq semiring_normalization_rules(18))
  then have "\<exists> b. b \<noteq> 0 \<and> 1/d = b^2"
   using assms(3) 
   by (metis \<open>1 / d \<noteq> 0\<close> power_divide zero_power2)
  then show "False"
   using \<open>\<not> (\<exists> b. b \<noteq> 0 \<and> 1/d = b^2)\<close> by blast
qed

lemma group_law:
  assumes "\<exists> b. 1/c = b^2" "\<not> (\<exists> b. b \<noteq> 0 \<and> 1/d = b^2)"
  shows "comm_group \<lparr>carrier = {(x,y). e x y = 0}, mult = add, one = (1,0)\<rparr>" 
proof(unfold_locales)
  {fix x1 y1 x2 y2
  assume "e x1 y1 = 0" "e x2 y2 = 0"
  have "e (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) = 0"
    apply(simp)
    using closure delta_non_zero[OF \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close> assms(1) assms(2)] 
          delta_def \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close> by auto}
  then show "
      \<And>x y. x \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
             y \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
           x \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub> y
           \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>" by auto
next
  {fix x1 y1 x2 y2 x3 y3 
   assume "e x1 y1 = 0" "e x2 y2 = 0" "e x3 y3 = 0" 
   then have "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
     using assms delta_non_zero by blast+
   fix x1' y1' x3' y3'
   assume "(x1',y1') = add (x1,y1) (x2,y2)"
          "(x3',y3') = add (x2,y2) (x3,y3)"
   then have "e x1' y1' = 0" "e x3' y3' = 0"
     using closure \<open>delta x1 y1 x2 y2 \<noteq> 0\<close> \<open>delta x2 y2 x3 y3 \<noteq> 0\<close> 
           \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close> \<open>e x3 y3 = 0\<close> delta_def by fastforce+
   then have "delta x1' y1' x3 y3 \<noteq> 0" "delta x1 y1 x3' y3' \<noteq> 0"
     using assms delta_non_zero \<open>e x3 y3 = 0\<close> apply blast
    by (simp add: \<open>e x1 y1 = 0\<close> \<open>e x3' y3' = 0\<close> assms delta_non_zero)

  have "add (add (x1,y1) (x2,y2)) (x3,y3) =
        add (x1,y1) (local.add (x2,y2) (x3,y3))"
    using associativity 
    by (metis \<open>(x1', y1') = add (x1, y1) (x2, y2)\<close> \<open>(x3', y3') = add (x2, y2) (x3, y3)\<close> \<open>delta x1 y1 x2 y2 \<noteq> 0\<close> 
              \<open>delta x1 y1 x3' y3' \<noteq> 0\<close> \<open>delta x1' y1' x3 y3 \<noteq> 0\<close> \<open>delta x2 y2 x3 y3 \<noteq> 0\<close> \<open>e x1 y1 = 0\<close> 
              \<open>e x2 y2 = 0\<close> \<open>e x3 y3 = 0\<close> delta_def mult_eq_0_iff)}

  then show "
    \<And>x y z.
       x \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
       y \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
       z \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
       x \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub>
       y \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub>
       z =
       x \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub>
      (y \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub>
       z)" by auto
next
  show "
   \<one>\<^bsub>\<lparr>carrier = {(x, y). e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub>
    \<in> carrier \<lparr>carrier = {(x, y). e x y = 0}, mult = local.add, one = (1, 0)\<rparr>"
    by (simp add: e_def)
next
  show "
   \<And>x. x \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
        \<one>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub> \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub> x = x"
    by (simp add: commutativity neutral)
next
  show "\<And>x. x \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
             x \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub>
         \<one>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub> = x"
    by (simp add: neutral)
next
  show "\<And>x y. x \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
              y \<in> carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr> \<Longrightarrow>
           x \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub> y =
           y \<otimes>\<^bsub>\<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>\<^esub> x"
    using commutativity by auto
next
  show "
   carrier \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>
   \<subseteq> Units \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add, one = (1, 0)\<rparr>"
  proof(simp,standard)
    fix z
    assume "z \<in> {(x, y). local.e x y = 0}"
    show "z \<in> Units
        \<lparr>carrier = {(x, y). local.e x y = 0}, mult = local.add,
           one = (1, 0)\<rparr>" 
      unfolding Units_def 
    proof(simp, cases "z", rule conjI) 
      fix x y
      assume "z = (x,y)" 
      from this \<open>z \<in> {(x, y). local.e x y = 0}\<close>
      show "case z of (x, y) \<Rightarrow> local.e x y = 0" by blast  
      then obtain x y where "z = (x,y)" "e x y = 0" by blast
      have "e x (-y) = 0" 
        using \<open>e x y = 0\<close> unfolding e_def by simp
      have "add (x,y) (x,-y) = (1,0)" 
        using inverse delta_non_zero assms \<open>e x y = 0\<close> by blast 
      then have "add (x,-y) (x,y) = (1,0)" by simp
      show "\<exists>a b. e a b = 0 \<and>
                  add (a, b) z = (1, 0) \<and> 
                  add z (a, b) = (1, 0)" 
        using \<open>add (x, y) (x, - y) = (1, 0)\<close> 
              \<open>e x (- y) = 0\<close> \<open>z = (x, y)\<close> by fastforce
    qed
  qed
qed
end

section\<open>Projective curves\<close>
(* Generalize for c \<noteq> 1 *)
locale ext_curve_addition = curve_addition +
  assumes c_eq_1: "c = 1" 
  assumes t_intro: "\<exists> b'. d = (b')^2"
  assumes t_ineq: "sqrt(d)^2 \<noteq> 1" "sqrt(d) \<noteq> 0"
begin

definition t where "t = sqrt(d)"
definition e' where "e' x y = x^2 + y^2 - 1 - t^2 * x^2 * y^2"


lemma c_d_pos: "d \<ge> 0" using t_intro by auto

lemma t_nz: "t \<noteq> 0" using t_def t_ineq(2) by auto

lemma d_nz: "d \<noteq> 0" using t_def t_nz by simp

lemma t_expr: "t^2 = d" "t^4 = d^2" using t_def t_intro by auto


 
text\<open>The case t^2 = 1 corresponds to a product of intersecting lines 
     which cannot be a group\<close>

lemma t_2_1_lines:
  "t^2 = 1 \<Longrightarrow> e' x y = - (1 - x^2) * (1 - y^2)" 
  unfolding e'_def by algebra

text\<open>The case t = 0 corresponds to a circle which has been treated before\<close>

lemma t_0_circle:
  "t = 0 \<Longrightarrow> e' x y = x^2 + y^2 - 1" 
  unfolding e'_def by auto

fun \<rho> :: "real \<times> real \<Rightarrow> real \<times> real" where 
  "\<rho> (x,y) = (-y,x)"
fun \<tau> :: "real \<times> real \<Rightarrow> real \<times> real" where 
  "\<tau> (x,y) = (1/(t*x),1/(t*y))"

fun ext_add :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real" where
 "ext_add (x1,y1) (x2,y2) =
    ((x1*y1-x2*y2) div (x2*y1-x1*y2),
     (x1*y1+x2*y2) div (x1*x2+y1*y2))"

lemma inversion_invariance_1:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  shows "add (\<tau> (x1,y1)) (x2,y2) = add (x1,y1) (\<tau> (x2,y2))"
  apply(simp)
  apply(subst c_eq_1)+
  apply(simp add: algebra_simps)
  apply(subst power2_eq_square[symmetric])+
  apply(subst t_expr)+
  apply(rule conjI)
  apply(simp add: divide_simps assms t_nz d_nz)
  apply(simp add: algebra_simps)
  apply(simp add: divide_simps assms t_nz d_nz)
  by(simp add: algebra_simps)

lemma inversion_invariance_2:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  shows "ext_add (\<tau> (x1,y1)) (x2,y2) = ext_add (x1,y1) (\<tau> (x2,y2))"
  apply(simp add: algebra_simps)
  apply(subst power2_eq_square[symmetric])+
  apply(subst t_expr)+
  apply(rule conjI)
  apply(simp add: divide_simps assms t_nz d_nz)
  apply(simp add: algebra_simps)
  apply(simp add: divide_simps assms t_nz d_nz)
  by(simp add: algebra_simps)

lemma rotation_invariance_1: 
  "add (\<rho> (x1,y1)) (x2,y2) = 
   \<rho> (fst (add (x1,y1) (x2,y2)),snd (add (x1,y1) (x2,y2)))"
  apply(simp)
  apply(subst c_eq_1)+
  by(simp add: algebra_simps divide_simps)

lemma rotation_invariance_2: 
  "ext_add (\<rho> (x1,y1)) (x2,y2) = 
   \<rho> (fst (ext_add (x1,y1) (x2,y2)),snd (ext_add (x1,y1) (x2,y2)))"
  by(simp add: algebra_simps divide_simps)

definition delta_x :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "delta_x x1 y1 x2 y2 = x2*y1 - x1*y2"
definition delta_y :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "delta_y x1 y1 x2 y2 = x1*x2 + y1*y2"
definition delta' :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "delta' x1 y1 x2 y2 = delta_x x1 y1 x2 y2 * delta_y x1 y1 x2 y2"

lemma rotation_invariance_3: 
  "delta x1 y1 (fst (\<rho> (x2,y2))) (snd (\<rho> (x2,y2))) = 
   delta x1 y1 x2 y2"
  by(simp add: delta_def delta_plus_def delta_minus_def,argo)

lemma rotation_invariance_4: 
  "delta' x1 y1 (fst (\<rho> (x2,y2))) (snd (\<rho> (x2,y2))) = 
   - delta' x1 y1 x2 y2"
  by(simp add: delta'_def delta_x_def delta_y_def,argo)

fun i :: "real \<times> real \<Rightarrow> real \<times> real" where 
  "i (a,b) = (a,-b)" 


lemma inverse_rule_1:
  "(\<tau> \<circ> i \<circ> \<tau>) (x,y) = i (x,y)" by (simp add: t_nz)
lemma inverse_rule_2:
  "(\<rho> \<circ> i \<circ> \<rho>) (x,y) = i (x,y)" by simp
lemma inverse_rule_3:
  "i (add (x1,y1) (x2,y2)) = add (i (x1,y1)) (i (x2,y2))"
  by(simp add: divide_simps)
lemma inverse_rule_4:
  "i (ext_add (x1,y1) (x2,y2)) = ext_add (i (x1,y1)) (i (x2,y2))"
  by(simp add: algebra_simps divide_simps)

(* Coherence and closure *)

lemma coherence_1:
  assumes "delta_x x1 y1 x2 y2 \<noteq> 0" "delta_minus x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "delta_x x1 y1 x2 y2 * delta_minus x1 y1 x2 y2 *
         (fst (ext_add (x1,y1) (x2,y2)) - fst (add (x1,y1) (x2,y2)))
         = x2 * y2 * e' x1 y1 - x1 * y1 * e' x2 y2"
  apply(simp)  
  apply(subst (2) delta_x_def[symmetric])
  apply(subst delta_minus_def[symmetric])
  apply(simp add: c_eq_1 assms(1,2) divide_simps)
  unfolding delta_minus_def delta_x_def e'_def
  apply(subst t_expr)+
  by(simp add: power2_eq_square field_simps)  
  
lemma coherence_2:
  assumes "delta_y x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "delta_y x1 y1 x2 y2 * delta_plus x1 y1 x2 y2 *
         (snd (ext_add (x1,y1) (x2,y2)) - snd (add (x1,y1) (x2,y2)))
         = - x2 * y2 * e' x1 y1 - x1 * y1 * e' x2 y2"
  apply(simp)  
  apply(subst (2) delta_y_def[symmetric])
  apply(subst delta_plus_def[symmetric])
  apply(simp add: c_eq_1 assms(1,2) divide_simps)
  unfolding delta_plus_def delta_y_def e'_def
  apply(subst t_expr)+
  by(simp add: power2_eq_square  field_simps)
  
lemma coherence:
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "ext_add (x1,y1) (x2,y2) = add (x1,y1) (x2,y2)"
  using coherence_1 coherence_2 delta_def delta'_def assms by auto

lemma closure:
  assumes "delta' x1 y1 x2 y2 \<noteq> 0"
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0" 
  assumes "(x3,y3) = ext_add (x1,y1) (x2,y2)"
  shows "e' x3 y3 = 0"
proof -
  have deltas_nz: "delta_x x1 y1 x2 y2 \<noteq> 0"
                  "delta_y x1 y1 x2 y2 \<noteq> 0"
    using assms(1) delta'_def by auto

  define closure1 where "closure1 =
    2 - t^2 + t^2 * x1^2 - 2 * x2^2 - t^2 * x1^2 * x2^2 + 
    t^2 * x2^4 + t^2 * y1^2 + t^4 * x1^2 * y1^2 - 
    t^2 * x2^2 * y1^2 - 2 * y2^2 - t^2 * x1^2 * y2^2 + 
    (4 * t^2 - 2 * t^4) * x2^2 * y2^2 - t^2 * y1^2 * y2^2 + 
    t^2 * y2^4"

  define closure2 where "closure2 = 
    -2 + t^2 + (2 - 2 * t^2) * x1^2 + t^2 * x1^4 + t^2 * x2^2 -
    t^2 * x1^2 * x2^2 + (2 - 2 * t^2) * y1^2 - t^2 * x2^2 * y1^2 + 
    t^2 * y1^4 + t^2 * y2^2 - t^2 * x1^2 * y2^2 + t^4 * x2^2 * y2^2 - 
    t^2 * y1^2 * y2^2"

  define p where "p = 
    -1 * t^4 * (x1^2 * x2^4 * y1^2 -x1^4 * x2^2 * y1^2 + 
    t^2 * x1^4 * y1^4 - x1^2 * x2^2 * y1^4 + x1^4 * x2^2 * y2^2 - 
    x1^2 * x2^4 * y2^2 - x1^4 * y1^2 * y2^2 + 4 * x1^2 * x2^2 * y1^2 * y2^2 - 
    2 * t^2 * x1^2 * x2^2 * y1^2 * y2^2 - x2^4 * y1^2 * y2^2 - x1^2 * y1^4 * y2^2 + 
    x2^2 * y1^4 * y2^2 - x1^2 * x2^2 * y2^4 + t^2 * x2^4 * y2^4 + x1^2 * y1^2 * y2^4 - 
    x2^2 * y1^2 * y2^4)"

  have v3: "x3 = fst (ext_add (x1,y1) (x2,y2))"
           "y3 = snd (ext_add (x1,y1) (x2,y2))"
    using assms(4) by simp+

  have "t^4 * (delta_x x1 y1 x2 y2)^2 * (delta_y x1 y1 x2 y2)^2 * e' x3 y3 = p"
    unfolding e'_def v3
    apply(simp)
    apply(subst (2) delta_x_def[symmetric])+
    apply(subst (2) delta_y_def[symmetric])+
    apply(subst power_divide)+
    apply(simp add: divide_simps deltas_nz)
    unfolding p_def delta_x_def delta_y_def
    by algebra    
  also have "... = closure1 * e' x1 y1 +  closure2 * e' x2 y2"
    unfolding p_def e'_def closure1_def closure2_def by algebra
  finally have "t^4 * (delta_x x1 y1 x2 y2)^2 * (delta_y x1 y1 x2 y2)^2 * e' x3 y3 =
                closure1 * e' x1 y1 +  closure2 * e' x2 y2" 
    by blast

  then show "e' x3 y3 = 0"
    using assms(2,3) deltas_nz t_nz by auto  
qed


end

locale projective_curve =
 ext_curve_addition
begin
  definition "e_aff = {(x,y). e' x y = 0}" 
  definition "e_circ = {(x,y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> (x,y) \<in> e_aff}"

  lemma "group (BijGroup (Reals \<times> Reals))"
    using group_BijGroup by blast

  lemma bij_\<rho>: "bij_betw \<rho> ((Reals - {0}) \<times> (Reals - {0})) 
                           ((Reals - {0}) \<times> (Reals - {0}))"
    unfolding bij_betw_def inj_on_def image_def
    apply(rule conjI,safe,auto)
    by (metis Reals_minus_iff add.inverse_neutral equation_minus_iff member_remove remove_def)

lemma bij_\<tau>: "bij_betw \<tau> ((Reals - {0}) \<times> (Reals - {0})) 
                         ((Reals - {0}) \<times> (Reals - {0}))"
    unfolding bij_betw_def inj_on_def image_def
    apply(rule conjI,safe)
    apply(simp add: t_nz)+
    apply(metis Reals_of_real mult.right_neutral real_scaleR_def scaleR_conv_of_real)
       apply (simp add: t_nz)
    apply (metis Reals_of_real mult.right_neutral real_scaleR_def scaleR_conv_of_real)
     apply (simp add: t_nz)
    apply(simp add: t_nz)
  proof -
    fix a :: real and b :: real
    assume a1: "a \<noteq> 0"
    assume a2: "(\<forall>x\<in>\<real> - {0}. a \<noteq> 1 / (t * x)) \<or> (\<forall>y\<in>\<real> - {0}. b \<noteq> 1 / (t * y))"
    obtain bb :: bool where
      f3: "(\<not> bb) = (\<forall>A_x. A_x \<notin> \<real> - {0} \<or> 1 / (t * A_x) \<noteq> a)"
      by (metis (full_types))
    have f4: "\<forall>R r ra. ((ra::real) = r \<or> ra \<in> R - {r}) \<or> ra \<notin> R"
      by blast
    have f5: "\<forall>r. (r::real) \<in> \<real>"
      by (metis (no_types) Reals_of_real mult.right_neutral real_scaleR_def scaleR_conv_of_real)
then have f6: "\<forall>r. (r = 0 \<or> bb) \<or> 1 / t / r \<noteq> a"
  using f4 f3 by (metis (no_types) divide_divide_eq_left)
  have f7: "\<forall>r ra. (ra::real) / (ra / r) = r \<or> ra = 0"
    by auto
  obtain bba :: bool where
    f8: "(\<not> bba) = (\<forall>X1. X1 \<notin> \<real> - {0} \<or> 1 / (t * X1) \<noteq> b)"
    by moura
  then have f9: "\<forall>r. (r = 0 \<or> bba) \<or> 1 / t / r \<noteq> b"
    using f5 f4 by (metis (no_types) divide_divide_eq_left)
  have "\<forall>r. (r::real) * 0 = 0 \<or> r = 0"
    by linarith
  then have bb
    using f7 f6 a1 by (metis divide_eq_0_iff mult.right_neutral t_nz)
  then show "b = 0"
    using f9 f8 f7 f3 a2 a1 by (metis divide_eq_0_iff t_nz)
qed
  
lemma "\<rho> \<in> carrier (BijGroup 
            ((Reals - {0}) \<times> (Reals - {0})))"
    unfolding BijGroup_def
    apply(simp)
    unfolding Bij_def extensional_def
    apply(simp, rule conjI)
    defer 1
    using bij_\<rho> apply blast
    apply(safe) 
       apply (metis Reals_of_real mult.right_neutral real_scaleR_def scaleR_conv_of_real)
    apply (metis Reals_of_real mult.right_neutral real_scaleR_def scaleR_conv_of_real)
    
end

end