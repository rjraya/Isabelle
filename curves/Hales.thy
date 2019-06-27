theory Hales
  imports Complex_Main
begin

context
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
    ((x1*x2 - c*y1*y2) div (1-d*x1*x2*y1*y2), 
     (x1*y2+y1*x2) div (1+d*x1*x2*y1*y2))"

lemma add_with_deltas:
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2), 
     (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2))"
  unfolding delta_minus_def delta_plus_def
  by(simp add: algebra_simps)

theorem commutativity: "add z1 z2 = add z2 z1"
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

  thm prod_eq_1 prod_eq_2
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
 (* review definition of Delta\<^sub>y with code *)
 define Delta\<^sub>y where "Delta\<^sub>y =
   (delta_plus x3' y3' x3 y3)*(delta_plus x1 y1 x1' y1')*
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

  have "gxpoly_expr = r1x * e1 + r2x * e2 + r3x * e3"
    unfolding gxpoly_expr_def r1x_def e1_def r2x_def e2_def r3x_def e3_def e_def             
    by algebra

  have x1'_expr: "x1' = (x1 * x2 - c * y1 * y2) / (1 - d * x1 * x2 * y1 * y2)"
    using assms(1,2,4,6) by(simp)
  have y1'_expr: "y1' = (x1 * y2 + y1 * x2) / (1 + d * x1 * x2 * y1 * y2)"
    using assms(1,2,4,6) by(simp)
  have x3'_expr: "x3' = (x2 * x3 - c * y2 * y3) / (1 - d * x2 * x3 * y2 * y3)"
    using assms(2,3,5,7) by(simp)
  have y3'_expr: "y3' = (x2 * y3 + y2 * x3) / (1 + d * x2 * x3 * y2 * y3)"
    using assms(2,3,5,7) by(simp)

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

  have "gxpoly = 
        ((x1' * x3 - c * y1' * y3) / delta_minus x1' y1' x3 y3 -
         (x1 * x3' - c * y1 * y3') / delta_minus x1 y1 x3' y3') *
        (delta_minus x1' y1' x3 y3 * delta_minus x1 y1 x3' y3' *
         delta x1 y1 x2 y2 * delta x2 y2 x3 y3)" 
    unfolding gxpoly_def g\<^sub>x_def Delta\<^sub>x_def
    apply(subst assms(4))
    apply(subst assms(1))
    apply(subst assms(5))
    apply(subst assms(3))
    apply(subst add_with_deltas)+
    by(simp)
  also have "... = 
     (x1' * x3 - c * y1' * y3) * delta_minus x1 y1 x3' y3' *
     delta x1 y1 x2 y2 * delta x2 y2 x3 y3 -
     (x1 * x3' - c * y1 * y3') * delta_minus x1' y1' x3 y3 *
     delta x1 y1 x2 y2 * delta x2 y2 x3 y3"
    by(simp add: divide_simps assms(8-15),argo)
  also have "... =   ((x1 * x2 - c * y1 * y2) / local.delta_minus x1 x2 y1 y2 *
     x3 -
     c *
     ((x1 * y2 + y1 * x2) / local.delta_plus x1 x2 y1 y2) *
     y3) *
    local.delta_minus x1 y1
     ((x2 * x3 - c * y2 * y3) / local.delta_minus x2 x3 y2 y3)
     ((x2 * y3 + y2 * x3) / local.delta_plus x2 x3 y2 y3) *
    (local.delta_plus x1 y1 x2 y2 *
     local.delta_minus x1 y1 x2 y2) *
    (local.delta_plus x2 y2 x3 y3 *
     local.delta_minus x2 y2 x3 y3) -
    (x1 *
     ((x2 * x3 - c * y2 * y3) /
      local.delta_minus x2 x3 y2 y3) -
     c * y1 *
     ((x2 * y3 + y2 * x3) / local.delta_plus x2 x3 y2 y3)) *
    local.delta_minus
     ((x1 * x2 - c * y1 * y2) / local.delta_minus x1 x2 y1 y2)
     ((x1 * y2 + y1 * x2) / local.delta_plus x1 x2 y1 y2) x3
     y3 *
    (local.delta_plus x1 y1 x2 y2 *
     local.delta_minus x1 y1 x2 y2) *
    (local.delta_plus x2 y2 x3 y3 *
     local.delta_minus x2 y2 x3 y3)"
    unfolding gxpoly_expr_def
    apply(subst x1'_expr)+
    apply(subst y1'_expr)+
    apply(subst x3'_expr)+
    apply(subst y3'_expr)+
    apply(subst delta_plus_def[symmetric])+
    apply(subst delta_minus_def[symmetric])+
    unfolding delta_def
    by simp
  also have "... = 
    ((x1 * x2 - c * y1 * y2) * local.delta_plus x1 y1 x2 y2 * x3 - c * ((x1 * y2 + y1 * x2) * local.delta_minus x1 y1 x2 y2) * y3) *
    local.delta_minus x1 y1 ((x2 * x3 - c * y2 * y3) / local.delta_minus x2 x3 y2 y3) ((x2 * y3 + y2 * x3) / local.delta_plus x2 x3 y2 y3) *
    (local.delta_plus x2 y2 x3 y3 * local.delta_minus x2 y2 x3 y3) 
   -
    (x1 * ((x2 * x3 - c * y2 * y3) * local.delta_plus x2 y2 x3 y3) - c * y1 * ((x2 * y3 + y2 * x3) * local.delta_minus x2 y2 x3 y3)) *
    local.delta_minus ((x1 * x2 - c * y1 * y2) / local.delta_minus x1 x2 y1 y2) ((x1 * y2 + y1 * x2) / local.delta_plus x1 x2 y1 y2) x3 y3 *
    (local.delta_plus x1 y1 x2 y2 * local.delta_minus x1 y1 x2 y2)"
    using delta_minus_def delta_plus_def
    apply(simp add: divide_simps assms(8-15))

  
  have "... = gxpoly_expr"
        
qed
    
end

end