theory Hales
  imports Complex_Main "HOL-Algebra.Group" "HOL-Algebra.Bij"
          "HOL-Library.Bit" Groebner_Bases.Groebner_Bases
          
begin

nitpick_params [verbose, card = 1-20, max_potential = 0,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 600]

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

lemma add_closure: 
  assumes "z3 = (x3,y3)" "z3 = add (x1,y1) (x2,y2)"
  assumes "delta_minus x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0"
  assumes "e x1 y1 = 0" "e x2 y2 = 0" 
  shows "e x3 y3 = 0" 
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

  define e1 where "e1 = e x1 y1"
  define e2 where "e2 = e x2 y2"

(*
  Exception!

  have prod_eq_1: "\<exists> r1 r2. 
      (e x3 y3)*(delta x1 y1 x2 y2)\<^sup>2 - (r1 * e1 + r2 * e2) = 0"
    unfolding prod_def e1_def e2_def e_def delta_def
              delta_plus_def delta_minus_def x3_expr y3_expr
    apply(algebra add: assms(5,6))
*)
  have prod_eq_1: "\<exists> r1 r2. prod - (r1 * e1 + r2 * e2) = 0"
    unfolding prod_def e1_def e2_def e_def by algebra

  define a where "a = x1*x2 - c*y1*y2"
  define b where "b = x1*y2+y1*x2"

  have "(e x3 y3)*(delta x1 y1 x2 y2)\<^sup>2 =
         e (a div (delta_minus x1 y1 x2 y2))
           (b div (delta_plus x1 y1 x2 y2)) * (delta x1 y1 x2 y2)\<^sup>2"
    unfolding a_def b_def
    by (simp add: mult.commute mult.left_commute x3_expr y3_expr)
  also have "... = 
    ((a div delta_minus x1 y1 x2 y2)\<^sup>2 +
    c * (b div delta_plus x1 y1 x2 y2)\<^sup>2 -
    1 -
    d * (a div delta_minus x1 y1 x2 y2)\<^sup>2 *
   (b div delta_plus x1 y1 x2 y2)\<^sup>2) * (delta x1 y1 x2 y2)\<^sup>2"
    unfolding delta_plus_def delta_minus_def delta_def e_def by simp
  also have "... = 
    ((a div delta_minus x1 y1 x2 y2)\<^sup>2 * (delta x1 y1 x2 y2)\<^sup>2 +
    c * (b div delta_plus x1 y1 x2 y2)\<^sup>2 * (delta x1 y1 x2 y2)\<^sup>2 -
    1 * (delta x1 y1 x2 y2)\<^sup>2 -
    d * (a div delta_minus x1 y1 x2 y2)\<^sup>2 *
   (b div delta_plus x1 y1 x2 y2)\<^sup>2 * (delta x1 y1 x2 y2)\<^sup>2)"
    by(simp add: algebra_simps)
  also have "... = 
    ((a * delta_plus x1 y1 x2 y2)\<^sup>2 + c * (b * delta_minus x1 y1 x2 y2)\<^sup>2 -
     (delta x1 y1 x2 y2)\<^sup>2 - d * a\<^sup>2 * b\<^sup>2)"
   unfolding delta_def by(simp add: field_simps assms(3,4))+
  also have "... - prod = 0"
    unfolding prod_def delta_plus_def delta_minus_def delta_def a_def b_def by algebra
  finally have "(e x3 y3)*(delta x1 y1 x2 y2)\<^sup>2 = prod" by simp
  then have prod_eq_2: "(e x3 y3) = prod div (delta x1 y1 x2 y2)\<^sup>2"
    using assms(3,4) delta_def by auto

  have "e1 = 0" unfolding e1_def using assms(5) by simp
  moreover have "e2 = 0" unfolding e2_def using assms(6) by simp
  ultimately have "prod = 0" using prod_eq_1 by simp
  then show "e x3 y3 = 0" using prod_eq_2 by simp
qed

lemma associativity: 
  assumes "z1' = (x1',y1')" "z3' = (x3',y3')"
  assumes "z1' = add (x1,y1) (x2,y2)" "z3' = add (x2,y2) (x3,y3)"
  assumes "delta_minus x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0"
          "delta_minus x2 y2 x3 y3 \<noteq> 0" "delta_plus x2 y2 x3 y3 \<noteq> 0"
          "delta_minus x1' y1' x3 y3 \<noteq> 0" "delta_plus x1' y1' x3 y3 \<noteq> 0"
          "delta_minus x1 y1 x3' y3' \<noteq> 0" "delta_plus x1 y1 x3' y3' \<noteq> 0"
  assumes "e x1 y1 = 0" "e x2 y2 = 0" "e x3 y3 = 0" 
  shows "add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))" 
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
 define g\<^sub>x :: real where "g\<^sub>x = fst(add z1' (x3,y3)) - fst(add (x1,y1) z3')"
 define g\<^sub>y where "g\<^sub>y = snd(add z1' (x3,y3)) - snd(add (x1,y1) z3')"
 define gxpoly where "gxpoly = g\<^sub>x * Delta\<^sub>x"
  define gypoly where "gypoly = g\<^sub>y * Delta\<^sub>y"

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
    using assms(1,3) by auto
  have y1'_expr: "y1' = (x1 * y2 + y1 * x2) / (1 + d * x1 * y1 * x2 * y2)"
    using assms(1,3) by auto
  have x3'_expr: "x3' = (x2 * x3 - c * y2 * y3) / (1 - d * x2 * y2 * x3 * y3)"
    using assms(2,4) by auto
  have y3'_expr: "y3' = (x2 * y3 + y2 * x3) / (1 + d * x2 * y2 * x3 * y3)"
    using assms(2,4) by auto
  
  have non_unfolded_adds:
      "delta x1 y1 x2 y2 \<noteq> 0" using delta_def assms(5,6) by auto
  
  have gx_div: "\<exists> r1 r2 r3. gxpoly_expr = r1 * e1 + r2 * e2 + r3 * e3"
    unfolding gxpoly_expr_def e1_def e2_def e3_def e_def 
    by algebra

  have gy_div: "\<exists> r1 r2 r3. gypoly_expr = r1 * e1 + r2 * e2 + r3 * e3"
    unfolding gypoly_expr_def e1_def e2_def e3_def e_def 
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
    by(simp add: divide_simps assms(5-8))

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
    by(simp add: divide_simps assms(5-8))

  have "gxpoly = gxpoly_expr"
    unfolding gxpoly_def g\<^sub>x_def Delta\<^sub>x_def 
    apply(simp add: assms(1,2))
    apply(subst delta_minus_def[symmetric])+
    apply(simp add: divide_simps assms(9,11))
    apply(subst (3) left_diff_distrib)
    apply(simp add: simp1gx simp2gx)
    unfolding delta_minus_def delta_plus_def (* equality *)
    unfolding gxpoly_expr_def
    by algebra

  obtain r1x r2x r3x where "gxpoly = r1x * e1 + r2x * e2 + r3x * e3"
    using \<open>gxpoly = gxpoly_expr\<close> gx_div by auto
  then have "gxpoly = 0" 
    using e1_def assms(13-15) e2_def e3_def by auto
  have "Delta\<^sub>x \<noteq> 0" 
    using Delta\<^sub>x_def delta_def assms(7-11) non_unfolded_adds by auto
  then have "g\<^sub>x = 0" 
    using \<open>gxpoly = 0\<close> gxpoly_def by auto

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
    by(simp add: divide_simps assms(5-8))

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
    by(simp add: divide_simps assms(5-8))

  have "gypoly = gypoly_expr"
    unfolding gypoly_def g\<^sub>y_def Delta\<^sub>y_def 
    apply(simp add: assms(1,2))
    apply(subst delta_plus_def[symmetric])+
    apply(simp add: divide_simps assms(10,12))
    apply(subst left_diff_distrib)
    apply(simp add: simp1gy simp2gy)
    unfolding delta_minus_def delta_plus_def (* equality *)
    unfolding gypoly_expr_def
    by algebra

  obtain r1y r2y r3y where "gypoly = r1y * e1 + r2y * e2 + r3y * e3"
    using \<open>gypoly = gypoly_expr\<close> gy_div by auto
  then have "gypoly = 0" 
    using e1_def assms(13-15) e2_def e3_def by auto
  have "Delta\<^sub>y \<noteq> 0" 
    using Delta\<^sub>y_def delta_def assms(7-12) non_unfolded_adds by auto
  then have "g\<^sub>y = 0" 
    using \<open>gypoly = 0\<close> gypoly_def by auto

  show ?thesis 
    using \<open>g\<^sub>y = 0\<close> \<open>g\<^sub>x = 0\<close> 
    unfolding g\<^sub>x_def g\<^sub>y_def assms(3,4)
    by (simp add: prod_eq_iff)
qed

lemma neutral: "add z (1,0) = z" by(cases "z",simp)

lemma inverse:
  assumes "e a b = 0" "delta_plus a b a b \<noteq> 0" 
  shows "add (a,b) (a,-b) = (1,0)" 
  using assms by(simp add: delta_plus_def e_def,algebra) 

corollary 
  assumes "e a b = 0" "delta_plus a b a b \<noteq> 0" 
  shows "delta_minus a b a (-b) \<noteq> 0" 
  using inverse[OF assms] assms(1) unfolding e_def delta_def delta_plus_def delta_minus_def
  by(simp)
  

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
    using add_closure delta_non_zero[OF \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close> assms(1) assms(2)] 
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
     using add_closure \<open>delta x1 y1 x2 y2 \<noteq> 0\<close> \<open>delta x2 y2 x3 y3 \<noteq> 0\<close> 
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
        using inverse[OF \<open>e x y = 0\<close> ] delta_non_zero[OF \<open>e x y = 0\<close> \<open>e x y = 0\<close> assms] delta_def by fastforce        
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

lemma e_e'_iff: "e x y = 0 \<longleftrightarrow> e' x y = 0"
  unfolding e_def e'_def using c_eq_1 t_expr(1) by simp

lemma t_sq_n1: "t^2 \<noteq> 1" using t_ineq(1) t_def by simp
 
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

lemma tau_sq: "(\<tau> \<circ> \<tau>) (x,y) = (x,y)" by(simp add: t_nz)

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
    sorry

definition G where
  "G \<equiv> {id,\<rho>,\<rho> \<circ> \<rho>,\<rho> \<circ> \<rho> \<circ> \<rho>,\<tau>,\<tau> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>}"

lemma g_no_fp:
  assumes "g \<in> G" "p \<in> e_circ" "g p = p" 
  shows "g = id"
proof -
  obtain x y where p_def: "p = (x,y)" by fastforce
  {assume "g = \<rho> \<or> g = \<rho> \<circ> \<rho> \<or> g = \<rho> \<circ> \<rho> \<circ> \<rho>"
  then consider (1) "g = \<rho>" | (2) "g = \<rho> \<circ> \<rho>" | (3) "g = \<rho> \<circ> \<rho> \<circ> \<rho>" by blast    
  note cases = this
  from cases have "x = 0" 
    apply(cases)
    using assms(3) p_def by(simp)+
  from cases have "y = 0" 
    apply(cases)
    using assms(3) p_def by(simp)+
  have "p \<notin> e_circ" using e_circ_def \<open>x = 0\<close> \<open>y = 0\<close> p_def by blast}
  note rotations = this
  {assume "g = \<tau> \<or> g = \<tau> \<circ> \<rho> \<or> g = \<tau> \<circ> \<rho> \<circ> \<rho> \<or> g = \<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>"
  then consider (1) "g = \<tau>" | (2) "g = \<tau> \<circ> \<rho>" | (3) "g = \<tau> \<circ> \<rho> \<circ> \<rho>" | (4) "g = \<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>" by blast
  note cases = this
  from cases have "2*t*x*y = 0 \<or> (t*x^2 \<in> {-1,1} \<and> t*y^2 \<in> {-1,1})"
    apply(cases)
    using assms(3) p_def 
    apply(simp,metis eq_divide_eq mult.left_commute power2_eq_square)
    using assms(3) p_def apply auto[1]
    using assms(3) p_def apply(simp)
    apply (smt c_d_pos real_sqrt_ge_0_iff t_def zero_le_divide_1_iff zero_le_mult_iff)
    using assms(3) p_def by auto[1]
  then have "t = 0 \<or> x = 0 \<or> y = 0 \<or>
    (t * x\<^sup>2 = - 1 \<or> t * x\<^sup>2 = 1) \<and> (t * y\<^sup>2 = - 1 \<or> t * y\<^sup>2 = 1)" 
    unfolding e'_def by(simp)
  then consider (1) "t = 0" | (2) "x = 0" | (3) "y = 0" |
             (4) "t * x\<^sup>2 = - 1 \<and> t * y\<^sup>2 = - 1" |
             (5) "t * x\<^sup>2 = - 1 \<and> t * y\<^sup>2 = 1" |
             (6) "t * x\<^sup>2 = 1 \<and> t * y\<^sup>2 = - 1" |
             (7) "t * x\<^sup>2 = 1 \<and> t * y\<^sup>2 = 1" by blast
  then have "e' x y = 2 * (1 - t) / t \<or> e' x y = 2 * (-1 - t) / t"
    unfolding e'_def
    apply(cases)
          apply(simp add: t_nz)
    using assms(2) unfolding e_circ_def p_def apply blast
    using assms(2) unfolding e_circ_def p_def apply blast
    apply (metis abs_of_nonneg c_d_pos c_eq_1 nonzero_mult_div_cancel_left one_neq_neg_one power2_eq_1_iff power2_minus real_sqrt_abs real_sqrt_ge_0_iff t_def t_intro t_nz zero_le_mult_iff zero_le_one zero_le_power_eq_numeral)
    apply (metis abs_of_nonneg c_d_pos c_eq_1 one_neq_neg_one power2_eq_1_iff power2_minus real_sqrt_abs real_sqrt_ge_0_iff t_def t_intro zero_le_mult_iff zero_le_one zero_le_power_eq_numeral)
    apply (metis abs_of_nonneg c_d_pos c_eq_1 one_neq_neg_one power2_eq_1_iff power2_minus real_sqrt_abs real_sqrt_ge_0_iff t_def t_intro zero_le_mult_iff zero_le_one zero_le_power_eq_numeral)
    proof -
      assume as: "t * x\<^sup>2 = 1 \<and> t * y\<^sup>2 = 1"
      then have "t\<^sup>2 * x\<^sup>2 * y\<^sup>2 = 1" by algebra
      then have "x\<^sup>2 + y\<^sup>2 - 1 - t\<^sup>2 * x\<^sup>2 * y\<^sup>2 = x\<^sup>2 + y\<^sup>2 - 2" by simp
      also have "... = 2 / t - 2" 
      proof -
        have "x\<^sup>2 = 1 / t" "y\<^sup>2 = 1 / t" using as t_nz 
          by(simp add: divide_simps,simp add: mult.commute)+
        then show ?thesis by simp
      qed
      also have "... = 2 * (1-t) / t"   
        using t_nz by(simp add: divide_simps)
      finally show "x\<^sup>2 + y\<^sup>2 - 1 - t\<^sup>2 * x\<^sup>2 * y\<^sup>2 = 2 * (1 - t) / t \<or>
                    x\<^sup>2 + y\<^sup>2 - 1 - t\<^sup>2 * x\<^sup>2 * y\<^sup>2 = 2 * (- 1 - t) / t" by blast
    qed
  then have "e' x y \<noteq> 0" 
    using t_sq_n1 t_nz by auto
  then have "p \<notin> e_circ" 
    unfolding e_circ_def e_aff_def p_def by blast}
  note symmetries = this
  from rotations symmetries 
  show ?thesis using G_def assms(1,2) by blast
qed

definition symmetries where 
  "symmetries = {\<tau>,\<tau> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>}"

definition rotations where
  "rotations = {id,\<rho>,\<rho> \<circ> \<rho>,\<rho> \<circ> \<rho> \<circ> \<rho>}"

lemma tau_rot_sym:
  assumes "r \<in> rotations"
  shows "\<tau> \<circ> r \<in> symmetries"
  using assms unfolding rotations_def symmetries_def by auto

definition e_aff_0 where
  "e_aff_0 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e_aff \<and> 
                                 (x2,y2) \<in> e_aff \<and> 
                                 delta x1 y1 x2 y2 \<noteq> 0 }"

definition e_aff_1 where
  "e_aff_1 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e_aff \<and> 
                                 (x2,y2) \<in> e_aff \<and> 
                                 delta' x1 y1 x2 y2 \<noteq> 0 }"

lemma dichotomy_1:
  assumes "p \<in> e_aff" "q \<in> e_aff" 
  shows "(p \<in> e_circ \<and> (\<exists> g \<in> symmetries. q = (g \<circ> i) p)) \<or>
         (p,q) \<in> e_aff_0 \<or> (p,q) \<in> e_aff_1" 
proof -
  obtain x1 y1 where p_def: "p = (x1,y1)" by fastforce
  obtain x2 y2 where q_def: "q = (x2,y2)" by fastforce

  consider (1) "(p,q) \<in> e_aff_0" |
           (2) "(p,q) \<in> e_aff_1" |
           (3) "\<not> ((p,q) \<in> e_aff_0) \<and> \<not> ((p,q) \<in> e_aff_1)" by blast
  then show ?thesis
  proof(cases)
    case 1 then show ?thesis by blast  
  next
    case 2 then show ?thesis by simp
  next
    case 3
    then have "delta x1 y1 x2 y2 = 0"
      unfolding p_def q_def  e_aff_0_def e_aff_1_def using assms 
      by (simp add: assms p_def q_def)
    from 3 have "delta' x1 y1 x2 y2 = 0"
      unfolding p_def q_def  e_aff_0_def e_aff_1_def using assms 
      by (simp add: assms p_def q_def)
    have "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
      using \<open>delta x1 y1 x2 y2 = 0\<close> 
      unfolding delta_def delta_plus_def delta_minus_def by auto
    then have "p \<in> e_circ" "q \<in> e_circ"
      unfolding e_circ_def using assms p_def q_def by blast+
    have "(\<exists> g \<in> symmetries. q = (g \<circ> i) p)" 
    proof -
      obtain a0 b0 where tq_expr: "\<tau> q = (a0,b0)" by fastforce
      obtain a1 b1 where "p = (a1,b1)" by fastforce
      have a0_nz: "a0 \<noteq> 0" "b0 \<noteq> 0"
        using \<open>\<tau> q = (a0, b0)\<close> \<open>x2 \<noteq> 0\<close> \<open>y2 \<noteq> 0\<close> comp_apply q_def tau_sq by auto 
      have a1_nz: "a1 \<noteq> 0" "b1 \<noteq> 0"
        using \<open>p = (a1, b1)\<close> \<open>x1 \<noteq> 0\<close> \<open>y1 \<noteq> 0\<close> p_def by auto
      define \<delta>' :: "real \<Rightarrow> real \<Rightarrow> real" where 
        "\<delta>'= (\<lambda> x0 y0. x0 * y0 * delta_minus a1 b1 (1/(t*x0)) (1/(t*y0)))" 
      define \<delta>_plus :: "real \<Rightarrow> real \<Rightarrow> real" where
        "\<delta>_plus = (\<lambda> x0 y0. t * x0 * y0 * delta_x a1 b1 (1/(t*x0)) (1/(t*y0)))"
      define \<delta>_minus :: "real \<Rightarrow> real \<Rightarrow> real" where
        "\<delta>_minus = (\<lambda> x0 y0. t * x0 * y0 * delta_y a1 b1 (1/(t*x0)) (1/(t*y0)))"
      show ?thesis
      proof(cases "delta_minus a1 b1 (fst q) (snd q) = 0")
        case True
        then have t1: "delta_minus a1 b1 (fst q) (snd q) = 0" by auto
        then show ?thesis 
        proof(cases "\<delta>_plus a0 b0 = 0")
          case True
          then have cas1: "delta_minus a1 b1 (fst q) (snd q) = 0"
                          "\<delta>_plus a0 b0 = 0" using t1 by auto
          have \<delta>'_expr: "\<delta>' a0 b0 = a0*b0 - a1*b1"
            unfolding \<delta>'_def delta_minus_def 
            apply(simp add: algebra_simps a0_nz a1_nz)
            apply(subst power2_eq_square[symmetric],subst t_expr(1))
            by(simp add: d_nz)
          then have eq1': "a0*b0 - a1*b1 = 0" 
          proof -
            have "(fst q) = (1 / (t * a0))" 
                 "(snd q) = (1 / (t * b0))"
              using tq_expr q_def tau_sq by auto
            then have "\<delta>' a0 b0 = a0 * b0 * delta_minus a1 b1 (fst q) (snd q)"
              unfolding \<delta>'_def by auto
            then show ?thesis using \<delta>'_expr cas1 by auto
          qed
          then have eq1: "a0 = a1 * (b1 / b0)"  
            using a0_nz(2) by(simp add: divide_simps) 
    
          have "0 = \<delta>_plus a0 b0"
            using cas1 by auto
          also have "\<delta>_plus a0 b0 = -a0*a1+b0*b1"
            unfolding \<delta>_plus_def delta_x_def 
            by(simp add: algebra_simps t_nz a0_nz)
          also have "... = b0*b1 - a1^2 * (b1 / b0)" 
            by(simp add: divide_simps a0_nz eq1 power2_eq_square[symmetric])
          also have "... = (b1 / b0) * (b0^2 - a1^2)"
            apply(simp add: divide_simps a0_nz)
            by(simp add: algebra_simps power2_eq_square[symmetric])
          finally have "(b1 / b0) * (b0^2 - a1^2) = 0" by auto
          then have eq2: "(b0^2 - a1^2) = 0" 
            by(simp add: a0_nz a1_nz)
    
          have "a0^2 - b1^2 = a1^2 * (b1^2 / b0^2) - b1^2"
            by(simp add: algebra_simps eq1 power2_eq_square)
          also have "... = (b1^2 / b0^2) * (a1^2 - b0^2)"
            by(simp add: divide_simps a0_nz right_diff_distrib')
          also have "... = 0" 
            using eq2 by auto
          finally have eq3: "a0^2 - b1^2 = 0" by blast
    
          from eq2 have pos1: "a1 = b0 \<or> a1 = -b0" by algebra
          from eq3 have pos2: "a0 = b1 \<or> a0 = -b1" by algebra
          have "(a0 = b1 \<and> a1 = b0) \<or> (a0 = -b1 \<and> a1 = -b0)"
            using pos1 pos2 eq2 eq3 eq1' by fastforce 
          then have "(a0,b0) = (b1,a1) \<or> (a0,b0) = (-b1,-a1)" by auto        
          then have "(a0,b0) \<in> {(b1,a1),(-b1,-a1)}" by simp
          moreover have "{(b1,a1),(-b1,-a1)} \<subseteq> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
            using \<open>p = (a1, b1)\<close> p_def by auto
          ultimately have "(a0,b0) \<in> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
            by blast
          then have "(\<exists> g \<in> rotations. \<tau> q = (g \<circ> i) p)"
            unfolding rotations_def by (simp add: \<open>\<tau> q = (a0, b0)\<close>)
          then obtain g where "g \<in> rotations \<and> \<tau> q = (g \<circ> i) p"
            by blast
          then have "q = (\<tau> \<circ> g \<circ> i) p"
            using tau_sq \<open>\<tau> q = (a0, b0)\<close> q_def by auto
          then show "(\<exists> g \<in> symmetries. q = (g \<circ> i) p)"
            unfolding symmetries_def rotations_def 
          using tau_rot_sym \<open>g \<in> rotations \<and> \<tau> q = (g \<circ> i) p\<close> symmetries_def by blast     
        next
          case False
           then have cas2: "delta_minus a1 b1 (fst q) (snd q) = 0"
                           "\<delta>_minus a0 b0 = 0"               
             using t1 apply blast
             using False \<delta>_minus_def \<delta>_plus_def \<open>delta' x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> delta'_def p_def q_def tq_expr by auto
           have \<delta>'_expr: "\<delta>' a0 b0 = a0*b0 - a1*b1"
             unfolding \<delta>'_def delta_minus_def 
             apply(simp add: algebra_simps a0_nz a1_nz)
             apply(subst power2_eq_square[symmetric],subst t_expr(1))
             by(simp add: d_nz)
           then have eq1': "a0*b0 - a1*b1 = 0" 
           proof -
             have "(fst q) = (1 / (t * a0))" 
                  "(snd q) = (1 / (t * b0))"
              using tq_expr q_def tau_sq by auto
              then have "\<delta>' a0 b0 = a0 * b0 * delta_minus a1 b1 (fst q) (snd q)"
                unfolding \<delta>'_def by auto
              then show ?thesis using \<delta>'_expr cas2 by auto 
            qed
            then have eq1: "a0 = a1 * (b1 / b0)"  
              using a0_nz(2) by(simp add: divide_simps) 

            have "0 = \<delta>_minus a0 b0"
              using cas2 by auto
            also have "\<delta>_minus a0 b0 = a0 * b1 + a1 * b0"
              unfolding \<delta>_minus_def delta_y_def 
              by(simp add: algebra_simps t_nz a0_nz)
            
            also have "... = a1 * (b1 / b0) * b1 + a1 * b0"
              by(simp add: eq1)
            also have "... = (a1^2 - b0^2)" 
              sorry 
            also have "... = b0*b1 - a1^2 * (b1 / b0)" 
                sorry
            also have "... = (b1 / b0) * (b0^2 - a1^2)"
              apply(simp add: divide_simps a0_nz)
              sorry
            finally have "(b1 / b0) * (b0^2 - a1^2) = 0" by auto
            then have eq2: "(b0^2 - a1^2) = 0" 
              by(simp add: a0_nz a1_nz)
    
          have "a0^2 - b1^2 = a1^2 * (b1^2 / b0^2) - b1^2"
            by(simp add: algebra_simps eq1 power2_eq_square)
          also have "... = (b1^2 / b0^2) * (a1^2 - b0^2)"
            by(simp add: divide_simps a0_nz right_diff_distrib')
          also have "... = 0" 
            using eq2 by auto
          finally have eq3: "a0^2 - b1^2 = 0" by blast
    
          from eq2 have pos1: "a1 = b0 \<or> a1 = -b0" by algebra
          from eq3 have pos2: "a0 = b1 \<or> a0 = -b1" by algebra
          have "(a0 = b1 \<and> a1 = b0) \<or> (a0 = -b1 \<and> a1 = -b0)"
            using pos1 pos2 eq2 eq3 eq1' by fastforce 
          then have "(a0,b0) = (b1,a1) \<or> (a0,b0) = (-b1,-a1)" by auto        
          then have "(a0,b0) \<in> {(b1,a1),(-b1,-a1)}" by simp
          moreover have "{(b1,a1),(-b1,-a1)} \<subseteq> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
            using \<open>p = (a1, b1)\<close> p_def by auto
          ultimately have "(a0,b0) \<in> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
            by blast
          then have "(\<exists> g \<in> rotations. \<tau> q = (g \<circ> i) p)"
            unfolding rotations_def by (simp add: \<open>\<tau> q = (a0, b0)\<close>)
          then obtain g where "g \<in> rotations \<and> \<tau> q = (g \<circ> i) p"
            by blast
          then have "q = (\<tau> \<circ> g \<circ> i) p"
            using tau_sq \<open>\<tau> q = (a0, b0)\<close> q_def by auto
          then show "(\<exists> g \<in> symmetries. q = (g \<circ> i) p)"
            unfolding symmetries_def rotations_def 
          using tau_rot_sym \<open>g \<in> rotations \<and> \<tau> q = (g \<circ> i) p\<close> symmetries_def by blast  
          qed
        next
          case False
         
          then show ?thesis sorry
        qed
      qed
      show ?thesis sorry
    qed
  qed

lemma dichotomy_2:
  assumes "p \<in> e_aff" "q \<in> e_aff" 
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "add (x1,y1) (x2,y2) = (1,0)" "((x1,y1),(x2,y2)) \<in> e_aff_0"
  shows "q = i p"
  sorry

lemma dichotomy_3:
  assumes "p \<in> e_aff" "q \<in> e_aff" 
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "add (x1,y1) (x2,y2) = (1,0)" "((x1,y1),(x2,y2)) \<in> e_aff_1"
  shows "q = i p"
  sorry

lemma tau_idemp: "\<tau> \<circ> \<tau> = id"
  using t_nz comp_def by auto

section \<open>Projective addition\<close>

definition gluing :: "(((real \<times> real) \<times> bit) \<times> ((real \<times> real) \<times> bit)) set" where
  "gluing = {(((x0,y0),l),((x1,y1),j)). 
               ((x0,y0) \<in> e_aff \<and> (x1,y1) \<in> e_aff) \<and>
               (((x0,y0) \<in> e_circ \<and> (x1,y1) = \<tau> (x0,y0) \<and> j = l+1) \<or>
                ((x0,y0) \<in> e_aff \<and> x0 = x1 \<and> y0 = y1 \<and> l = j))}"

lemma gluing_char:
  assumes "(((x0,y0),l),((x1,y1),j)) \<in> gluing"
  shows "((x0,y0) = (x1,y1) \<and> l = j) \<or> 
          ((x1,y1) = \<tau> (x0,y0) \<and> l = j+1)"
  using assms gluing_def by force+

lemma gluing_char_zero:
  assumes "(((x0,y0),l),((x1,y1),j)) \<in> gluing" "x0 = 0 \<or> y0 = 0"
  shows "(x0,y0) = (x1,y1) \<and> l = j"
proof - 
  consider (1) "x0 = 0" | (2) "y0 = 0" using assms by auto
  then show ?thesis
    apply(cases)
    using assms(1) unfolding gluing_def 
    by(simp add: e_circ_def)+
qed



definition "Bits = range Bit"
definition e_aff_bit :: "((real \<times> real) \<times> bit) set" where
 "e_aff_bit = e_aff \<times> Bits"

lemma eq_rel: "equiv e_aff_bit gluing"
  unfolding equiv_def
proof(intro conjI)
  show "refl_on e_aff_bit gluing"
    unfolding refl_on_def
  proof 
    show "(\<forall>x\<in>e_aff_bit. (x, x) \<in> gluing)"
      unfolding e_aff_bit_def gluing_def by auto
    have "range Bit = (UNIV::bit set)" 
      by (simp add: type_definition.Abs_image[OF type_definition_bit]) 
    show "gluing \<subseteq> e_aff_bit \<times> e_aff_bit" 
      unfolding e_aff_bit_def gluing_def Bits_def
      using \<open>range Bit = (UNIV::bit set)\<close> by auto
  qed
  
  show "sym gluing" 
    unfolding sym_def gluing_def
    by(auto simp add: e_circ_def t_nz)
  
  show "trans gluing"
    unfolding trans_def gluing_def
     by(auto simp add: e_circ_def t_nz)
qed

definition e_proj where "e_proj = e_aff_bit // gluing"

lemma rho_circ: 
  assumes "p \<in> e_circ"
  shows "\<rho> p \<in> e_circ"
  using assms unfolding e_circ_def e_aff_def e'_def 
  by(simp split: prod.splits,argo) 

lemma i_circ:
  assumes "(x,y) \<in> e_circ"
  shows "i (x,y) \<in> e_circ"
  using assms unfolding e_circ_def e_aff_def e'_def by auto

lemma rot_circ:
  assumes "p \<in> e_circ" "tr \<in> rotations"
  shows "tr p \<in> e_circ"
proof -
  consider (1) "tr = id" | (2) "tr = \<rho>"  | (3) "tr = \<rho> \<circ> \<rho>" | (4) "tr = \<rho> \<circ> \<rho> \<circ> \<rho>"
    using assms(2) unfolding rotations_def by blast
  then show ?thesis by(cases,auto simp add: assms(1) rho_circ)          
qed
  
lemma \<tau>_circ:
  assumes "p \<in> e_circ"
  shows "\<tau> p \<in> e_circ"
  using assms unfolding e_circ_def 
  apply(simp split: prod.splits) 
  apply(simp add: divide_simps t_nz)
  unfolding e_aff_def e'_def
  apply(simp split: prod.splits) 
  apply(simp add: divide_simps t_nz)
  apply(subst power_mult_distrib)+
  apply(subst ring_distribs(1)[symmetric])+
  apply(subst (1) mult.assoc)
  apply(subst right_diff_distrib[symmetric])
  apply(simp add: t_nz)
  by(simp add: algebra_simps)

lemma e_proj_eq:
  assumes "p \<in> e_proj"
  shows "\<exists> x y l. (p = {((x,y),l)} \<or> p = {((x,y),l),(\<tau> (x,y),l+1)}) \<and> (x,y) \<in> e_aff"        
proof -
  obtain g where p_expr: "p = gluing `` {g}" "g \<in> e_aff_bit"
    using assms unfolding e_proj_def quotient_def by blast+
  then obtain x y l where g_expr: "g = ((x,y),l)" "(x,y) \<in> e_aff" 
    using e_aff_bit_def by auto
  then have p_simp: "p = gluing `` {((x,y),l)}" "((x,y),l) \<in> e_aff_bit" "(x,y) \<in> e_aff"
    using p_expr by simp+
  {fix x' y' l'
  assume "((x',y'), l') \<in> gluing `` {((x,y),l)}"
  then have "(x' = x \<and> y' = y \<and> l' = l) \<or>
        ((x',y') = \<tau> (x,y) \<and> l' = l + 1)" 
    unfolding gluing_def Image_def by auto}
  note pair_form = this
  have "p = {((x,y),l), (\<tau> (x,y), l+1)} \<or> p = {((x,y),l)}" 
  proof -
    have "((x,y),l) \<in> p" 
      using p_simp eq_rel unfolding equiv_def refl_on_def by blast
    then show ?thesis using pair_form p_simp by auto
  qed    
  then show ?thesis using p_simp by auto
qed

lemma rot_comp:
  assumes "t1 \<in> rotations" "t2 \<in> rotations"
  shows "t1 \<circ> t2 \<in> rotations"
  using assms unfolding rotations_def by auto


  
(*
function proj_add :: "(real \<times> real) \<times> bit \<Rightarrow> (real \<times> real) \<times> bit \<Rightarrow> (real \<times> real) \<times> bit" where
  "proj_add ((x1,y1),l) ((x2,y2),j) = ((add (x1,y1) (x2,y2)), l+j)" 
    if "delta x1 y1 x2 y2 \<noteq> 0 \<and> (x1,y1) \<in> e_aff \<and> (x2,y2) \<in> e_aff"
| "proj_add ((x1,y1),l) ((x2,y2),j) = ((ext_add (x1,y1) (x2,y2)), l+j)" 
    if "delta' x1 y1 x2 y2 \<noteq> 0 \<and> (x1,y1) \<in> e_aff \<and> (x2,y2) \<in> e_aff"
| "proj_add ((x1,y1),l) ((x2,y2),j) = undefined"
    if "delta x1 y1 x2 y2 = 0 \<and> delta' x1 y1 x2 y2 = 0 \<or> (x1,y1) \<notin> e_aff \<or> (x2,y2) \<notin> e_aff"
  apply(fast,fastforce)
  using coherence e_aff_def by auto

definition proj_add_class where
"proj_add_class c1 c2 = (case_prod proj_add) ` ({x. proj_add_dom x} \<inter> (c1 \<times> c2))"
*)
definition p_delta :: "(real \<times> real) \<times> bit \<Rightarrow> (real \<times> real) \<times> bit \<Rightarrow> real" where 
  "p_delta p1 p2 = 
    delta (fst (fst p1)) (snd (fst p1)) (fst (fst p2)) (snd (fst p2))"

definition p_delta' :: "(real \<times> real) \<times> bit \<Rightarrow> (real \<times> real) \<times> bit \<Rightarrow> real" where 
  "p_delta' p1 p2 = 
    delta' (fst (fst p1)) (snd (fst p1)) (fst (fst p2)) (snd (fst p2))"

partial_function (option) proj_add :: 
  "(real \<times> real) \<times> bit \<Rightarrow> (real \<times> real) \<times> bit \<Rightarrow> ((real \<times> real) \<times> bit) option" where
  "
  proj_add p1 p2 =  
    (
      if (p_delta p1 p2 \<noteq> 0 \<and> fst p1 \<in> e_aff \<and> fst p2 \<in> e_aff) 
      then Some (add (fst p1) (fst p2), (snd p1) + (snd p2))
      else 
        (
          if (p_delta' p1 p2 \<noteq> 0 \<and> fst p1 \<in> e_aff \<and> fst p2 \<in> e_aff)   
          then Some (ext_add (fst p1) (fst p2), (snd p1) + (snd p2))
          else None
        )
    )
  "

definition "proj_add_class c1 c2 =
  ((case_prod (\<lambda> x y. the (proj_add x y))) ` (Map.dom (case_prod proj_add) \<inter> (c1 \<times> c2))) // gluing"

lemma rot_com:
  assumes "tr \<in> rotations"
  shows "tr \<circ> \<tau> = \<tau> \<circ> tr"
  using assms unfolding rotations_def by(auto)

lemma rot_inv:
  assumes "r \<in> rotations"
  shows "\<exists> r' \<in> rotations. r' \<circ> r = id" 
  using assms unfolding rotations_def by force

lemma group_lem:
  assumes "r' \<in> rotations" "r \<in> rotations"
  assumes "(r' \<circ> i) (x,y) = (\<tau> \<circ> r) (i (x, y))"
  shows "\<exists> r''. r'' \<in> rotations \<and> i (x,y) = (\<tau> \<circ> r'') (i (x,y))" 
proof -
  obtain r'' where "r'' \<circ> r' = id" "r'' \<in> rotations" using rot_inv assms(1) by blast
  then have "i (x,y) = (r'' \<circ> \<tau> \<circ> r) (i (x, y))"
    using assms(3) by (simp,metis pointfree_idE)
  then have "i (x,y) = (\<tau> \<circ> r'' \<circ> r) (i (x, y))"
    using rot_com[OF \<open>r'' \<in> rotations\<close>] by simp
  then show ?thesis using rot_comp[OF \<open>r'' \<in> rotations\<close> assms(2)] by auto    
qed

lemma tau_not_id: "\<tau> \<noteq> id"
  apply(simp add: fun_eq_iff) 
  by (metis c_eq_1 eq_divide_eq_1 mult_cancel_left2 one_power2 t_def t_ineq(1))

lemma sym_not_id:
  assumes "r \<in> rotations"
  shows "\<tau> \<circ> r \<noteq> id"
  using assms unfolding rotations_def 
  apply(subst fun_eq_iff,simp)
  apply(auto)
  using tau_not_id apply auto[1]
  apply (metis d_nz)
  apply (metis eq_divide_eq_1 minus_mult_minus mult.right_neutral ring_normalization_rules(1) semiring_normalization_rules(29) t_expr(1) t_sq_n1)
  by (metis d_nz)

lemma covering:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "proj_add_class p q \<noteq> {}"
proof -
  have "p \<in> e_aff_bit // gluing"
    using assms(1) unfolding e_proj_def by blast
  from e_proj_eq[OF assms(1)] e_proj_eq[OF assms(2)]
  obtain x y l x' y' l' where 
    p_q_expr: "p = {((x, y), l)} \<or> p = {((x, y), l), (\<tau> (x, y), l + 1)} " 
    "q = {((x', y'), l')} \<or> q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
    "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    by blast
  then have gluings: "p = (gluing `` {((x,y),l)})" 
                     "q = (gluing `` {((x',y'),l')})"
    using assms(1) assms(2) unfolding e_proj_def 
    using Image_singleton_iff equiv_class_eq_iff[OF eq_rel] insertI1 quotientE
    by metis+
  consider 
     "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | "((x, y), x', y') \<in> e_aff_0" 
   | "((x, y), x', y') \<in> e_aff_1"
    using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by blast
  then show ?thesis 
  proof(cases)
    case 1
    then obtain r where eq: "(x',y') = (\<tau> \<circ> r) (i (x,y))" "r \<in> rotations"
      unfolding symmetries_def rotations_def by force
    then have "\<tau> \<in> G" unfolding G_def by auto
    have "i (x,y) \<in> e_circ"
      using 1 unfolding e_circ_def e_aff_def e'_def by auto
    then have "(\<tau> \<circ> r \<circ> i) (x, y) \<in> e_circ" 
      using i_circ rho_circ rot_circ \<tau>_circ eq(2) by auto
    have "\<tau> (x',y') \<noteq> (\<tau> \<circ> r \<circ> i) (x,y)"
      unfolding eq(1) 
      using g_no_fp[OF \<open>\<tau> \<in> G\<close> \<open>(\<tau> \<circ> r \<circ> i) (x, y) \<in> e_circ\<close>] 
      apply(simp)
      by (metis \<tau>.simps c_eq_1 d_nz divide_divide_eq_left fst_conv id_apply mult.assoc mult_cancel_right1 power2_eq_square semiring_normalization_rules(11) t_expr(1) t_sq_n1)
    have "\<tau> (x',y') \<in> e_aff" 
      using \<open>(\<tau> \<circ> r \<circ> i) (x, y) \<in> e_circ\<close> eq e_circ_def \<tau>_circ by auto
    
    have "\<tau> (x',y') \<in> e_circ" 
      using \<tau>_circ \<open>(\<tau> \<circ> r \<circ> i) (x, y) \<in> e_circ\<close> eq(1) by auto 
    then have "(\<tau> (x',y'),l'+1) \<in> (gluing `` {((x',y'),l')})"
      unfolding gluing_def Image_def 
      apply(simp split: prod.splits del: \<tau>.simps,safe)
      apply (simp add: p_q_expr(4))
      using \<open>\<tau> (x', y') \<in> e_aff\<close> apply auto[1]
      using \<open>(\<tau> \<circ> r \<circ> i) (x, y) \<in> e_circ\<close> eq(1) by auto
    then have sc: "(gluing `` {((x',y'),l')}) = (gluing `` {(\<tau> (x',y'),l'+1)})"
      by (meson Image_singleton_iff eq_rel equiv_class_eq_iff)
    have "proj_add_class p q =
          proj_add_class (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')})"
      using gluings by simp
    also have "... = 
          proj_add_class (gluing `` {((x,y),l)}) (gluing `` {(\<tau> (x',y'),l'+1)})"
      using sc by simp
    finally have eq_simp: "proj_add_class p q = proj_add_class (gluing `` {((x,y),l)}) (gluing `` {(\<tau> (x',y'),l'+1)})"
      by blast

    consider
      "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (x', y') = (g \<circ> i) (x, y))" 
    | "((x, y), \<tau> (x', y')) \<in> e_aff_0" 
    | "((x, y), \<tau> (x', y')) \<in> e_aff_1"
      using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>\<tau> (x', y') \<in> e_aff\<close>] by blast  
    then show ?thesis
    proof(cases)
      case 1
      define q' where "q' = \<tau> (x',y')"
      from 1 have "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. q' = (g \<circ> i) (x, y))"
        by(simp add: q'_def)  
      then obtain r' where eq1: "q' = (\<tau> \<circ> r') (i (x,y))" "r' \<in> rotations"
        unfolding symmetries_def rotations_def by force
      then have "\<tau> (x',y') = (\<tau> \<circ> r') (i (x,y))" 
        by(simp add: q'_def)  
      then have "(x',y') = (r' \<circ> i) (x,y)" 
        using tau_sq apply(simp del: \<tau>.simps) by (metis surj_pair)
      then have "(r' \<circ> i) (x,y) = (\<tau> \<circ> r) (i (x, y))"
        using eq by simp
      then obtain r'' where eq2: "i (x,y) = (\<tau> \<circ> r'') (i (x,y))" "r'' \<in> rotations"
        using group_lem[OF \<open>r' \<in> rotations\<close> \<open>r \<in> rotations\<close>] by blast
      have "\<tau> \<circ> r'' \<in> G" 
        using G_def \<open>r'' \<in> rotations\<close> rotations_def 
        apply(simp) 
        using G_def \<open>(r' \<circ> i) (x, y) = (\<tau> \<circ> r) (i (x, y))\<close> symmetries_def tau_rot_sym by auto
      have "i (x,y) \<in> e_circ" 
        using \<open>i (x, y) \<in> e_circ\<close> by auto
      have "\<tau> \<circ> r'' \<noteq> id"
        using sym_not_id[OF \<open>r'' \<in> rotations\<close>] by blast
      then have "False"
        using g_no_fp[OF \<open>\<tau> \<circ> r'' \<in> G\<close> \<open>i (x,y) \<in> e_circ\<close> eq2(1)[symmetric]]
        by blast
      then show ?thesis by blast
    next
      case 2
      define x'' where "x'' = fst (\<tau> (x',y'))"
      define y'' where "y'' = snd (\<tau> (x',y'))"
      from 2 have "delta x y x'' y'' \<noteq> 0"
        unfolding e_aff_0_def using x''_def y''_def by simp 
      then obtain v where add_some: "proj_add ((x,y),l) ((x'',y''),l'+1) = Some v"
        using proj_add.simps[of "((x,y),l)" "((x'',y''),l'+1)"] p_q_expr
        unfolding p_delta_def 
        using \<open>\<tau> (x', y') \<in> e_aff\<close> fst_conv x''_def y''_def by auto
      have in_set: "(((x,y),l),((x'',y''),l'+1)) \<in> (dom (\<lambda>(x, y). proj_add x y) \<inter> p \<times> q)"
        unfolding dom_def using p_q_expr 
        apply(simp del: \<tau>.simps)
        apply(rule conjI)
        apply (metis add_some surjective_pairing)
        apply(rule conjI)     
        apply blast
        using \<open>(\<tau> (x', y'), l' + 1) \<in> gluing `` {((x', y'), l')}\<close> gluings(2) x''_def y''_def by auto
      then show ?thesis 
        unfolding proj_add_class_def 
        using add_some in_set by blast
    next
      case 3
      define x'' where "x'' = fst (\<tau> (x',y'))"
      define y'' where "y'' = snd (\<tau> (x',y'))"
      from 3 have "delta' x y x'' y'' \<noteq> 0"
        unfolding e_aff_1_def using x''_def y''_def by simp 
      then obtain v where add_some: "proj_add ((x,y),l) ((x'',y''),l'+1) = Some v"
        using proj_add.simps[of "((x,y),l)" "((x'',y''),l'+1)"] p_q_expr
        unfolding p_delta'_def 
        using \<open>\<tau> (x', y') \<in> e_aff\<close> fst_conv x''_def y''_def 
        by (metis prod.collapse snd_conv)
      have in_set: "(((x,y),l),((x'',y''),l'+1)) \<in> (dom (\<lambda>(x, y). proj_add x y) \<inter> p \<times> q)"
        unfolding dom_def using p_q_expr 
        apply(simp del: \<tau>.simps)
        apply(rule conjI)
        apply (metis add_some surjective_pairing)
        apply(rule conjI)     
        apply blast
        using \<open>(\<tau> (x', y'), l' + 1) \<in> gluing `` {((x', y'), l')}\<close> gluings(2) x''_def y''_def by auto
      then show ?thesis 
        unfolding proj_add_class_def 
        using add_some in_set by blast
  qed
  next
    case 2
    then have "delta x y x' y' \<noteq> 0" 
      unfolding e_aff_0_def by simp
    then obtain v where add_some: "proj_add ((x,y),l) ((x',y'),l') = Some v"
      using proj_add.simps[of "((x,y),l)" "((x',y'),l')"] p_q_expr
      unfolding p_delta_def by auto
    then have in_set: "(((x,y),l),((x',y'),l')) \<in> (dom (\<lambda>(x, y). proj_add x y) \<inter> p \<times> q)"
      unfolding dom_def using p_q_expr by fast
    then show ?thesis 
      unfolding proj_add_class_def 
      using add_some in_set by blast
  next
    case 3
    then have "delta' x y x' y' \<noteq> 0" 
      unfolding e_aff_1_def by simp
    then obtain v where add_some: "proj_add ((x,y),l) ((x',y'),l') = Some v"
      using proj_add.simps[of "((x,y),l)" "((x',y'),l')"] p_q_expr
      unfolding p_delta'_def by fastforce
    then have in_set: "(((x,y),l),((x',y'),l')) \<in> (dom (\<lambda>(x, y). proj_add x y) \<inter> p \<times> q)"
      unfolding dom_def using p_q_expr by fast
    then show ?thesis 
      unfolding proj_add_class_def 
      using add_some in_set by blast
  qed
qed

lemma wd_d_nz:
  assumes "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" "(x,y) \<in> e_circ"
  shows "delta x y x' y' = 0"
  using assms unfolding symmetries_def e_circ_def delta_def delta_minus_def delta_plus_def
  by(auto,auto simp add: divide_simps t_nz t_expr(1) power2_eq_square[symmetric] d_nz)

lemma wd_d'_nz:
  assumes "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" "(x,y) \<in> e_circ"
  shows "delta' x y x' y' = 0"
  using assms unfolding symmetries_def e_circ_def delta'_def delta_x_def delta_y_def
  by(auto)

(* This kind of lemma may vary with different fields *)
lemma e_aff_x0:
  assumes "x = 0" "(x,y) \<in> e_aff"
  shows "y = 1 \<or> y = -1"
  using assms unfolding e_aff_def e'_def
  by(simp,algebra)

lemma e_aff_y0:
  assumes "y = 0" "(x,y) \<in> e_aff"
  shows "x = 1 \<or> x = -1"
  using assms unfolding e_aff_def e'_def
  by(simp,algebra) 

lemma add_ext_add:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0"
  shows "ext_add (x1,y1) (x2,y2) = \<tau> (add (\<tau> (x1,y1)) (x2,y2))"
  apply(simp)
  apply(rule conjI)
  apply(simp add: c_eq_1)
  apply(simp add: divide_simps t_nz power2_eq_square[symmetric] assms t_expr(1) d_nz)
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1)) 
  apply(simp add: divide_simps t_nz power2_eq_square[symmetric] assms t_expr(1) d_nz)
  by(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1)) 

corollary add_ext_add_2:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0"
  shows "add (x1,y1) (x2,y2) = \<tau> (ext_add (\<tau> (x1,y1)) (x2,y2))"
proof -
  obtain x1' y1' where tau_expr: "\<tau> (x1,y1) = (x1',y1')" by simp
  then have p_nz: "x1' \<noteq> 0" "y1' \<noteq> 0" 
    using assms(1) tau_sq apply auto[1]
    using \<open>\<tau> (x1, y1) = (x1', y1')\<close> assms(2) tau_sq by auto
  have "add (x1,y1) (x2,y2) = add (\<tau> (x1', y1')) (x2, y2)"
    using tau_expr tau_idemp 
    by (metis comp_apply id_apply)
  also have "... = \<tau> (ext_add (x1', y1') (x2, y2))"
    using add_ext_add[OF p_nz assms(3,4)] tau_idemp by simp
  also have "... = \<tau> (ext_add (\<tau> (x1, y1)) (x2, y2))"
    using tau_expr tau_idemp by auto
  finally show ?thesis by blast
qed

lemma gluing_inv:
  assumes "x \<noteq> 0" "y \<noteq> 0" "(x,y) \<in> e_aff"
  shows "gluing `` {((x,y),j)} = gluing `` {(\<tau> (x,y),j+1)}"
proof
  have tr: "\<tau> (x,y) \<in> e_aff" "\<tau> (x,y) \<in> e_circ"
      using e_circ_def assms \<tau>_circ by fastforce+ 
  show "gluing `` {((x,y), j)} \<subseteq> gluing `` {(\<tau> (x,y), j + 1)}"
  proof     
    fix p b
    assume as: "(p, b) \<in> gluing `` {((x,y), j)}"
    then have "(p,b) \<in> e_aff_bit"
      unfolding e_aff_bit_def gluing_def 
      using as e_aff_bit_def eq_rel equiv_class_eq_iff by fastforce   
    have in_glue: "(((x,y), j), p, b) \<in> gluing" using as by blast
    have "(p = (x,y) \<and> b = j) \<or> (p = \<tau> (x,y) \<and> b = j+1)"
      using gluing_char in_glue 
      by (smt add.assoc add.commute add.left_neutral add.right_neutral bit_add_eq_1_iff prod.collapse)
    then consider
      (1) "p = (x,y)" "b = j" |
      (2) "p = \<tau> (x,y)" "b = j+1" by blast
    then have "((\<tau> (x,y), j + 1), p, b) \<in> gluing" 
      apply(cases)
      using tr unfolding gluing_def by(simp add: t_nz assms)+
    then show "(p, b) \<in> gluing `` {(\<tau> (x,y), j + 1)}" by blast
  qed

  show "gluing `` {(\<tau> (x, y), j + 1)} \<subseteq> gluing `` {((x, y), j)}"
  proof     
    fix p b
    assume as: "(p, b) \<in> gluing `` {(\<tau> (x, y), j + 1)}"
    then have "(p,b) \<in> e_aff_bit"
      unfolding e_aff_bit_def gluing_def 
      using as e_aff_bit_def eq_rel equiv_class_eq_iff by fastforce  
    obtain x' y' where p_expr: "p = (x',y')" by fastforce
    obtain xt yt where tau_expr: "\<tau> (x,y) = (xt,yt)" by simp
    have in_glue: "((\<tau> (x, y), j + 1), p, b) \<in> gluing" using as by blast
    then have in_glue_coord: "(((xt,yt), j + 1), (x',y'), b) \<in> gluing" 
      using \<open>p = (x',y')\<close> \<open>\<tau> (x,y) = (xt,yt)\<close> by auto
    have "(p = (x,y) \<and> b = j) \<or> (p = \<tau> (x,y) \<and> b = j+1)"
      using gluing_char[OF in_glue_coord] p_expr tau_expr 
      apply(simp add: algebra_simps del: \<tau>.simps)
      using pointfree_idE tau_idemp by force
    then consider
      (1) "p = (x,y)" "b = j" |
      (2) "p = \<tau> (x,y)" "b = j+1" by blast
    then have "(((x,y), j), p, b) \<in> gluing" 
      apply(cases)
      using \<open>(p, b) \<in> e_aff_bit\<close> eq_rel equiv_class_eq_iff apply fastforce
      using tr unfolding gluing_def by(simp add: e_circ_def assms)
    then show "(p, b) \<in> gluing `` {((x,y), j)}" by blast
  qed
qed 

(*lemma 
  assumes "gluing `` {((x0,y0),l)} \<in> e_proj" "gluing `` {((x1,y1),j)} \<in> e_proj"
          "x0 = 0 \<or> y0 = 0 \<or> x1 = 0 \<or> y1 = 0" "(x0,y0) \<in> e_aff" "(x1,y1) \<in> e_aff"
  shows "card (proj_add_class p q) = 1"
proof -
  consider (1) "x0 = 0" | (2) "y0 = 0" | (3) "x1 = 0" | (4) "y1 = 0" using assms by blast
  then show ?thesis
  proof(cases)
    case 1
    have x_expr: "y0 = 1 \<or> y0 = -1"
      using e_aff_x0[OF 1 assms(4)]  by simp
    have "(0, y0) \<in> e_aff \<and> (x1, y1) \<in> e_aff" 
      using assms 1 by blast
    have "delta x0 y0 x1 y1 \<noteq> 0" 
      unfolding delta_def delta_plus_def delta_minus_def
      using 1 by simp
    have d_0_nz: "delta 0 y0 x1 y1 \<noteq> 0" 
      unfolding delta_def delta_plus_def delta_minus_def by auto
    have "(0, 1 / (t * y0)) \<notin> e_aff"
            using \<open>(x0,y0) \<in> e_aff\<close> 1 unfolding e_aff_def e'_def 
            apply(simp add: divide_simps t_sq_n1 t_nz,safe)
            by (simp add: power_mult_distrib t_sq_n1)
    have v1: "proj_add ((0, y0), l) ((x1, y1), j) = Some ((- (c * y0 * y1), y0 * x1), l + j)"
      apply(simp add: proj_add.simps \<open>(x0,y0) \<in> e_aff\<close> p_delta_def d_0_nz)
      using \<open>(0, y0) \<in> e_aff \<and> (x1, y1) \<in> e_aff\<close> by simp
    have v2: "proj_add ((0, y0), l) (\<tau> (x1, y1), j + 1) = Some v"
      apply(simp add: proj_add.simps \<open>(x0,y0) \<in> e_aff\<close> p_delta_def d_0_nz t_nz)
      
    have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((0, y), l), (x', 0), l'),
                   (((x, y), l), \<tau> (x', 0), l' + 1)}) = 
                {(((x, y), l), (x', 0), l')}" 
            using v1 v2 by auto
          show ?thesis 
            unfolding 2 apply(simp add: bb t_nz del: \<tau>.simps)
            unfolding proj_add_class_def apply(simp add: dom_eq del: \<tau>.simps)
            unfolding quotient_def by auto
    then show ?thesis 
      
      sorry
  next
    case 2
    then show ?thesis sorry
  next
    case 3
    then show ?thesis sorry
  next
    case 4
    then show ?thesis sorry
  qed

have x_expr: "x' = 1 \<or> x' = -1"
            using e_aff_y0[OF bb \<open>(x',y') \<in> e_aff\<close>] by simp
          have "delta x y x' y' \<noteq> 0" 
            unfolding delta_def delta_plus_def delta_minus_def
            using bb by simp
          have d_0_nz: "delta x y x' 0 \<noteq> 0" 
            unfolding delta_def delta_plus_def delta_minus_def by auto
          have "(1 / (t * x'),0) \<notin> e_aff"
            unfolding e_aff_def e'_def 
            using \<open>(x',y') \<in> e_aff\<close> bb unfolding e_aff_def e'_def 
            apply(simp add: divide_simps t_sq_n1 t_nz,safe)
            by (simp add: power_mult_distrib t_sq_n1)
          have v1: "proj_add ((x, y), l) ((x', 0), l') = Some ((x * x', y * x'), l + l')"
            apply(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> p_delta_def d_0_nz)
            using b bb unfolding e_aff_0_def by simp
          have v2: "proj_add ((x, y), l) (\<tau> (x', 0), l' + 1) = None"
            apply(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> p_delta_def d_0_nz)
            by(simp add: \<open>(1 / (t * x'),0) \<notin> e_aff\<close>)
          have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((x, y), l), (x', 0), l'),
                   (((x, y), l), \<tau> (x', 0), l' + 1)}) = 
                {(((x, y), l), (x', 0), l')}" 
            using v1 v2 by auto
          show ?thesis 
            unfolding 2 apply(simp add: bb t_nz del: \<tau>.simps)
            unfolding proj_add_class_def apply(simp add: dom_eq del: \<tau>.simps)
            unfolding quotient_def by auto
*)

lemma eq_class_simp:
  assumes "X \<in> e_aff_bit // gluing" "X \<noteq> {}"
  shows "X // gluing = {X}"
proof
  {
    fix x
    assume "x \<in> X"
    have "gluing `` {x} = X"
      by (metis Image_singleton_iff \<open>x \<in> X\<close> equiv_class_eq_iff[OF eq_rel] quotientE[OF assms(1)])
  }
  note simp_un = this
  show "X // gluing \<subseteq> {X}"
    unfolding quotient_def by(simp add: simp_un)
  show "{X} \<subseteq> X // gluing"
    unfolding quotient_def by(simp add: simp_un assms)
qed

lemma eq_class_image:
  assumes "(x,y) \<in> e_aff" 
  shows "(gluing `` {((x,y), l)}) // gluing = 
         {gluing `` {((x,y), l)}}"
proof(rule eq_class_simp)
  have "((x,y),l) \<in> e_aff_bit" 
    using assms unfolding e_aff_bit_def Bits_def 
    by (metis Bit_cases SigmaI image_eqI)
  then show "gluing `` {((x, y), l)} \<in> e_aff_bit // gluing"
    by (simp add: quotientI)
  show "gluing `` {((x, y), l)} \<noteq> {}" 
    using \<open>gluing `` {((x, y), l)} \<in> e_aff_bit // gluing\<close> e_proj_def e_proj_eq by fastforce
qed

lemma gluing_class:
  assumes "x \<noteq> 0" "y \<noteq> 0" "(x,y) \<in> e_aff"
  shows "gluing `` {((x,y), l)} = {((x,y), l), (\<tau> (x,y), l + 1)}"
proof - 
  have "(x,y) \<in> e_circ" using assms unfolding e_circ_def by blast
  then have "\<tau> (x,y) \<in> e_aff"
    using \<tau>_circ using e_circ_def by force
  show ?thesis
    unfolding gluing_def Image_def
    apply(simp split: prod.splits add: e_circ_def \<open>\<tau> (x,y) \<in> e_aff\<close> assms del: \<tau>.simps \<rho>.simps,safe)
    by(auto simp del: \<tau>.simps, simp add: assms,simp add: \<open>\<tau> (x,y) \<in> e_aff\<close> del: \<tau>.simps)
qed

lemma add_cancel:
  assumes "e x0 y0 = 0" "e x1 y1 = 0" 
  assumes "delta x0 y0 x1 y1 \<noteq> 0" "delta x0 y0 x2 y2 \<noteq> 0" 
  assumes "add (x0,y0) (x1,y1) = add (x0,y0) (x2,y2)"
  assumes "x0 \<noteq> 0" "y0 \<noteq> 0"
  shows "(x1,y1) = (x2,y2)"
proof -
  have "delta x0 (-y0) x1 y1 \<noteq> 0"  
    using assms(2)
    unfolding delta_def delta_plus_def delta_minus_def by auto
  have x0_rules: "delta_plus x0 y0 x0 y0 \<noteq> 0" 
    unfolding delta_plus_def
    apply(subst (1) mult.assoc,subst (2) mult.assoc,subst (1) mult.assoc)
    apply(subst power2_eq_square[symmetric])
    using mult_nonneg_nonneg[OF c_d_pos zero_le_power2[of "x0*y0"]] by auto
  have "delta_plus x0 (-y0) x0 y0 \<noteq> 0"      
    unfolding delta_plus_def 
    apply(simp)
    apply(subst (1) mult.assoc,subst (2) mult.assoc,subst (1) mult.assoc)
    apply(subst power2_eq_square[symmetric])
    using assms(1) unfolding e_def
    apply(simp add: c_eq_1)
    thm inverse
    sorry

  have s_rules: "d * x0 * y0 * x1 * y1 \<noteq> 1"
                "1 + d * x0 * y0 * x1 * y1 \<noteq> 0"
                "1 + d * x0 * y0 * x0 * y0 \<noteq> 0" 
                "1 - d * x0 * y0 * x1 * y1 \<noteq> 0" 
    using assms(3,5) x0_rules
    unfolding delta_def delta_plus_def delta_minus_def 
    by auto
  have "add (x0,-y0) (x0,y0) = (1,0)" 
    using inverse[OF assms(1) \<open>delta_plus x0 y0 x0 y0 \<noteq> 0\<close>] by fastforce
  then have 1: "(x1,y1) = add (add (x0,-y0) (x0,y0)) (x1,y1)"
    using neutral commutativity by simp
  also have "... = add (x0,-y0) (add (x0,y0) (x1,y1))"
  proof(cases "delta x0 y0 x0 (-y0) = 0")
    case True
    then have "1 - d * x0 * y0 * x0 * y0 = 0" 
      using \<open>delta_plus x0 (- y0) x0 y0 \<noteq> 0\<close>
      unfolding delta_def delta_minus_def delta_plus_def 
      by(simp add: s_rules(3))     
    have "(x1,y1) = add (x0,-y0) (add (x0,y0) (x1,y1))"
      apply(simp,safe,simp add: c_eq_1)
      apply(simp add: divide_simps s_rules,safe,simp add: algebra_simps)
      using assms(1,2) unfolding e_def apply(simp add: c_eq_1,algebra)
      using \<open>delta_plus x0 (- y0) x0 y0 \<noteq> 0\<close> True \<open>1 - d * x0 * y0 * x0 * y0 = 0\<close> delta_plus_def apply auto[1]
      apply(simp add: c_eq_1,simp add: divide_simps s_rules,safe)
      using assms(1,2) unfolding e_def apply(simp add: c_eq_1,algebra)
      using \<open>delta_plus x0 (- y0) x0 y0 \<noteq> 0\<close> True \<open>1 - d * x0 * y0 * x0 * y0 = 0\<close> delta_plus_def by auto
    then show ?thesis using 1 by argo
  next
    case False
    then have s_rules_2: "delta_minus x0 (- y0) x0 y0 \<noteq> 0"
                       "delta_plus x0 (- y0) x0 y0 \<noteq> 0"
                       "delta_minus x0 y0 x1 y1 \<noteq> 0"
                       "delta_plus x0 y0 x1 y1 \<noteq> 0"
                       "delta_minus (fst (add (x0, - y0) (x0, y0))) (snd (add (x0, - y0) (x0, y0))) x1 y1 \<noteq> 0"
         "delta_plus (fst (add (x0, - y0) (x0, y0))) (snd (add (x0, - y0) (x0, y0))) x1 y1 \<noteq> 0"
      using assms(3)
      unfolding delta_def delta_plus_def delta_minus_def by auto
    have e_rules: "e x0 (- y0) = 0" 
      using assms(1) unfolding e_def by fastforce
    show ?thesis
    proof(cases "delta x0 (- y0) (fst (add (x0, y0) (x1, y1))) (snd (add (x0, y0) (x1, y1))) \<noteq> 0")
      case True
      then have s_rules_3: 
        "delta_minus x0 (- y0) (fst (add (x0, y0) (x1, y1))) (snd (add (x0, y0) (x1, y1))) \<noteq> 0"
        "delta_plus x0 (- y0) (fst (add (x0, y0) (x1, y1))) (snd (add (x0, y0) (x1, y1))) \<noteq> 0"
        unfolding delta_def by auto
      then show ?thesis 
        using associativity[of _ _ _ _ _ _ x0 "-y0"  x0 y0 x1 y1,
                        OF _ _ _ _ s_rules_2 s_rules_3 e_rules assms(1,2)]
        by fastforce
    next
      case False
      then consider
        (1) "delta_minus x0 (- y0) (fst (add (x0, y0) (x1, y1)))
             (snd (add (x0, y0) (x1, y1))) = 0" |
        (2) "delta_plus x0 (- y0) (fst (add (x0, y0) (x1, y1)))
             (snd (add (x0, y0) (x1, y1))) = 0" unfolding delta_def by fastforce
      then show ?thesis
      proof(cases)
        case 1
        then have "(x1,y1) = add (x0, - y0) (add (x0, y0) (x1, y1))"
          unfolding delta_minus_def
          apply(simp)
          apply(rule conjI)
           apply(simp add: c_eq_1)
           apply(simp add: divide_simps s_rules)
          apply(simp add: algebra_simps) 
          using assms(1,2) unfolding e_def apply(simp add: c_eq_1)
          
          apply(simp add: divide_simps s_rules,safe) 
             apply(simp add: algebra_simps)
          defer 1
             apply algebra
            apply(simp add: divide_simps s_rules,safe) 
          apply simp 
          apply argo 
          apply simp 
             apply(simp add: divide_simps s_rules)
            apply(simp add: divide_simps s_rules) 
           apply(simp add: divide_simps s_rules d_nz assms(6,7),safe)
            apply (simp add: s_rules(1) s_rules(2))
           apply (simp add: s_rules(1) s_rules(2))          
          
          sorry
      next
        case 2
        then have "(x1,y1) = add (x0, - y0) (add (x0, y0) (x1, y1))"
          unfolding delta_plus_def
           apply(simp)
          apply(simp add: c_eq_1)
          using assms(1,2) unfolding e_def apply(simp add: c_eq_1)
          apply(simp add: divide_simps s_rules,safe) 
          apply(argo,simp,argo,argo,fastforce,argo) 
               apply(simp add: divide_simps s_rules)
              apply(simp add: divide_simps s_rules)
             apply(simp add: divide_simps s_rules)
            apply(simp add: divide_simps s_rules)
           apply algebra
          apply(simp add: divide_simps s_rules d_nz assms(6,7)) 
          apply(simp add: algebra_simps)
          sledgehammer

          sorry
      qed
       
    qed
    have "delta_plus x0 (- y0) (fst (add (x0, y0) (x1, y1))) (snd (add (x0, y0) (x1, y1))) \<noteq> 0"
      unfolding delta_plus_def 
      using assms(1,2) unfolding e_def 
      apply(simp add: divide_simps s_rules) 
      apply(simp add: c_eq_1 ) 
      sorry
    have "delta_minus x0 (- y0) (fst (add (x0, y0) (x1, y1))) (snd (add (x0, y0) (x1, y1))) \<noteq> 0"
      unfolding delta_minus_def 
      using assms(1,2) unfolding e_def 
      apply(simp add: divide_simps s_rules)
      apply(simp add: c_eq_1 )
      sorry
    
    show ?thesis 
      
      sorry
  qed
  have "(x1,y1) = add (x0,-y0) (add (x0,y0) (x1,y1))"
    apply(simp,safe)
    apply(simp add: c_eq_1)
     apply(simp add: divide_simps s_rules,safe)
      apply(simp add: algebra_simps)
    using assms(1,2) unfolding e_def apply(simp add: c_eq_1)
      apply algebra
     using \<open>delta_plus x0 (- y0) x0 y0 \<noteq> 0\<close> assms(5) curve_addition.delta_def curve_addition.delta_minus_def curve_addition.delta_plus_def s_rules(3) apply auto[1]
     apply(simp add: c_eq_1) 
     apply(simp add: divide_simps s_rules,safe)
     using assms(1,2) unfolding e_def apply(simp add: c_eq_1)
      apply algebra
     using \<open>delta_plus x0 (- y0) x0 y0 \<noteq> 0\<close> assms(5) curve_addition.delta_def curve_addition.delta_minus_def curve_addition.delta_plus_def s_rules(3) by auto
    try0
  also have "... = add (x0,-y0) (add (x0,y0) (x1,y1))"
    apply(simp)
    apply(simp add: c_eq_1)
    using assms(1,2) unfolding e_def apply(simp add: c_eq_1)
    apply(simp add: divide_simps s_rules d_nz assms(6,7),safe)
    apply algebra
                  apply algebra
                 apply(simp add: divide_simps s_rules d_nz assms(6,7))
                 apply algebra

    defer 1
                 apply algebra
                apply algebra
               apply algebra
             apply algebra

            defer 1
             defer 1
             apply fastforce 
           apply algebra

          defer 1
          defer 1
           apply(simp add: divide_simps s_rules d_nz assms(6,7))
         apply algebra
        apply(simp add: divide_simps s_rules d_nz assms(6,7))         
    sorry

theorem well_defined:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "card (proj_add_class p q) = 1"
proof -
  from e_proj_eq[OF assms(1)] e_proj_eq[OF assms(2)]
  obtain x y l x' y' l' where 
    p_q_expr: "(p = {((x, y), l)} \<or> p = {((x, y), l), (\<tau> (x, y), l + 1)})" 
              "(x, y) \<in> e_aff" 
              "(q = {((x', y'), l')} \<or> q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)})"
              "(x', y') \<in> e_aff" by blast
  then consider
           (1) "p = {((x, y), l)}" "q = {((x', y'), l')}" |
           (2) "p = {((x, y), l)}" "q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" |
           (3) "p = {((x, y), l), (\<tau> (x, y), l + 1)}" "q = {((x', y'), l')}" |
           (4) "p = {((x, y), l), (\<tau> (x, y), l + 1)}" "q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" by argo 
    then show ?thesis
    proof(cases)
      case 1
      then have "proj_add_class p q = proj_add_class {((x, y), l)} {((x', y'), l')}"
        by auto
      then obtain v where v_expr: "proj_add ((x, y), l) ((x', y'), l') = Some v"
        using covering[OF assms] unfolding proj_add_class_def by auto
      have s_map: "(\<lambda>(x, y). the (proj_add x y)) ` (dom (\<lambda>(x, y). proj_add x y) \<inter> p \<times> q) = 
            {v}"
        unfolding image_def dom_def 1 apply(simp add: v_expr)
      proof -
        have "(\<exists>a b ba. v = ((a, b), ba))" 
          by (metis surjective_pairing)
        then show "{y. y = v \<and> (\<exists>a b ba. v = ((a, b), ba))} = {v}" by simp
      qed
      show ?thesis 
        unfolding proj_add_class_def apply(simp add: s_map)
        using assms(1) unfolding 1 e_proj_def quotient_def by auto
    next
      case 2    
  
      consider
        (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
        (b) "((x, y), x', y') \<in> e_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
        (c) "((x, y), x', y') \<in> e_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))"
        using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by blast
      then show ?thesis 
      proof(cases)
        case a
        then obtain g where "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" by auto        
        then have "delta x y x' y' = 0" "delta' x y x' y' = 0"
          using wd_d_nz wd_d'_nz a by auto 
        then have one_none: "proj_add ((x, y), l) ((x', y'), l') = None"
          using proj_add.simps unfolding p_delta_def p_delta'_def by auto
        have "(dom (\<lambda>(x, y). proj_add x y) \<inter> {((x, y), l)} \<times> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}) \<noteq> {}"
          using covering[OF assms] unfolding 2 proj_add_class_def by blast
        then have s_simp: 
          "(dom (\<lambda>(x, y). proj_add x y) \<inter> 
            {((x, y), l)} \<times> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}) 
           = {(((x, y), l),(\<tau> (x', y'), l' + 1))}" 
          using one_none by auto
        show "card(proj_add_class p q) = 1"
          unfolding proj_add_class_def 2
          apply(subst s_simp)
          unfolding quotient_def by auto
      next
        case b
        then have ld_nz: "delta x y x' y' \<noteq> 0" 
          unfolding e_aff_0_def by auto    
        consider 
          (aa) "x' = 0" |
          (bb) "y' = 0" |
          (cc) "x' \<noteq> 0" "y' \<noteq> 0" by blast
        then show ?thesis
        proof(cases)
          case aa
          have y_expr: "y' = 1 \<or> y' = -1"
            using e_aff_x0[OF aa \<open>(x',y') \<in> e_aff\<close>] by simp
          have "delta x y x' y' \<noteq> 0" 
            unfolding delta_def delta_plus_def delta_minus_def
            using aa by simp
          have d_0_nz: "delta x y 0 y' \<noteq> 0" 
            unfolding delta_def delta_plus_def delta_minus_def by auto
          have "(0, 1 / (t * y')) \<notin> e_aff"
            using \<open>(x',y') \<in> e_aff\<close> aa unfolding e_aff_def e'_def 
            apply(simp add: divide_simps t_sq_n1 t_nz,safe)
            by (simp add: power_mult_distrib t_sq_n1)
          have v1: "proj_add ((x, y), l) ((0, y'), l') = Some ((- (c * y * y'), x * y'), l + l')"
            apply(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> p_delta_def d_0_nz)
            using b aa unfolding e_aff_0_def by simp
          have v2: "proj_add ((x, y), l) (\<tau> (0, y'), l' + 1) = None"
            apply(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> p_delta_def d_0_nz)
            by(simp add: \<open>(0, 1 / (t * y')) \<notin> e_aff\<close>)
          have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((x, y), l), (0, y'), l'),
                   (((x, y), l), \<tau> (0, y'), l' + 1)}) = 
                {(((x, y), l), (0, y'), l')}" 
            using v1 v2 by auto
          show ?thesis 
            unfolding 2 apply(simp add: aa t_nz del: \<tau>.simps)
            unfolding proj_add_class_def apply(simp add: dom_eq del: \<tau>.simps)
            unfolding quotient_def by auto
        next
          case bb
          have x_expr: "x' = 1 \<or> x' = -1"
            using e_aff_y0[OF bb \<open>(x',y') \<in> e_aff\<close>] by simp
          have "delta x y x' y' \<noteq> 0" 
            unfolding delta_def delta_plus_def delta_minus_def
            using bb by simp
          have d_0_nz: "delta x y x' 0 \<noteq> 0" 
            unfolding delta_def delta_plus_def delta_minus_def by auto
          have "(1 / (t * x'),0) \<notin> e_aff"
            unfolding e_aff_def e'_def 
            using \<open>(x',y') \<in> e_aff\<close> bb unfolding e_aff_def e'_def 
            apply(simp add: divide_simps t_sq_n1 t_nz,safe)
            by (simp add: power_mult_distrib t_sq_n1)
          have v1: "proj_add ((x, y), l) ((x', 0), l') = Some ((x * x', y * x'), l + l')"
            apply(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> p_delta_def d_0_nz)
            using b bb unfolding e_aff_0_def by simp
          have v2: "proj_add ((x, y), l) (\<tau> (x', 0), l' + 1) = None"
            apply(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> p_delta_def d_0_nz)
            by(simp add: \<open>(1 / (t * x'),0) \<notin> e_aff\<close>)
          have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((x, y), l), (x', 0), l'),
                   (((x, y), l), \<tau> (x', 0), l' + 1)}) = 
                {(((x, y), l), (x', 0), l')}" 
            using v1 v2 by auto
          show ?thesis 
            unfolding 2 apply(simp add: bb t_nz del: \<tau>.simps)
            unfolding proj_add_class_def apply(simp add: dom_eq del: \<tau>.simps)
            unfolding quotient_def by auto
        next
          case cc
          
          have "(x',y') \<in> e_circ"
            unfolding e_circ_def using cc \<open>(x',y') \<in> e_aff\<close> by blast
          then have "\<tau> (x', y') \<in> e_circ" 
            using cc \<tau>_circ by blast
          then have "\<tau> (x', y') \<in> e_aff"
            unfolding e_circ_def by force
            
          have v1: "proj_add ((x, y), l) ((x', y'), l') = Some (add (x, y) (x', y'), l + l')"
            by(simp add: proj_add.simps \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> p_delta_def ld_nz del: add.simps)
          consider 
            (z1) "x = 0" |
            (z2) "y = 0" |
            (z3) "x \<noteq> 0" "y \<noteq> 0" by blast
          then show ?thesis
          proof(cases)
            case z1
            then have y_expr: "y = 1 \<or> y = -1"
              using \<open>(x,y) \<in> e_aff\<close> unfolding e_aff_def e'_def 
              by(simp,algebra)
            then have "y*y = 1" by auto
            have "add (x, y) (x', y') = \<rho> (y*x',y*y')"
              by(simp add: z1,simp add: c_eq_1)
            then have v1_def: "proj_add ((x, y), l) ((x', y'), l') = 
                               Some (\<rho> (y*x',y*y'), l + l')"
              using v1 by simp
            have "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
              unfolding delta_def delta_plus_def delta_minus_def
              using z1 by simp
            then have v2: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = 
                       Some (add (x, y) (\<tau> (x', y')), l+l'+1)"
              using proj_add.simps p_delta_def 
              using \<open>\<tau> (x', y') \<in> e_aff\<close> p_q_expr(2) by auto 
            have "add (x, y) (\<tau> (x', y')) = \<rho> (y*(fst (\<tau> (x', y'))),y*(snd (\<tau> (x', y'))))"
              by(simp add: z1, simp add: c_eq_1)
            then have "add (x, y) (\<tau> (x', y')) = (\<rho> \<circ> \<tau>) (y*x',y*y')"
              apply(simp)
              apply(rule conjI)
              by(simp add: divide_simps t_nz cc y_expr \<open>y*y = 1\<close>)+
            then have v2_def: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) =
                          Some (\<tau> (\<rho> (y*x',y*y')), l+l'+1)"
              using v2 rot_com rotations_def by auto
            have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((0, y), l), (x', y'), l'),
                   (((0, y), l), \<tau> (x', y'), l' + 1)}) = 
                {(((0, y), l), (x', y'), l'), (((0, y), l), \<tau> (x', y'), l' + 1)}" 
              using v1_def v2_def z1 by auto
            have rho_aff: "\<rho> (y * x', y * y') \<in> e_aff"
                using \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> unfolding e_aff_def e'_def
                apply(cases "y = 1")
                apply(simp add: z1,argo) 
                using y_expr by(simp add: z1,argo) 
            have eq: "{(\<rho> (y * x', y * y'), l + l'), (\<tau> (\<rho> (y * x', y * y')), l + l' + 1)}
                      = gluing `` {(\<rho> (y * x', y * y'), l + l')}"
            proof -
              have coord: "fst (\<rho> (y * x', y * y')) \<noteq> 0" "snd (\<rho> (y * x', y * y')) \<noteq> 0" 
                using y_expr cc by auto
              show ?thesis
                using gluing_class[OF coord(1) coord(2)] rho_aff by simp
            qed
            show ?thesis
              unfolding 2 apply(simp add: t_nz z1 del: \<tau>.simps)
              unfolding proj_add_class_def apply(simp add: dom_eq del: \<tau>.simps)
              apply(subst z1[symmetric])+
              apply(subst v1_def,subst v2_def,simp del: \<tau>.simps \<rho>.simps)
              apply(subst eq)   
              using eq_class_image rho_aff by fastforce
          next
            case z2
            then have x_expr: "x = 1 \<or> x = -1"
              using \<open>(x,y) \<in> e_aff\<close> unfolding e_aff_def e'_def 
              by(simp,algebra)
            then have "x*x = 1" by auto
            have "add (x, y) (x', y') = (x*x',x*y')"
              by(simp add: z2)
            then have v1_def: "proj_add ((x, y), l) ((x', y'), l') = 
                               Some ((x*x',x*y'), l + l')"
              using v1 by simp
            have "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
              unfolding delta_def delta_plus_def delta_minus_def
              using z2 by simp
            then have v2: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = 
                       Some (add (x, y) (\<tau> (x', y')), l+l'+1)"
              using proj_add.simps p_delta_def 
              using \<open>\<tau> (x', y') \<in> e_aff\<close> p_q_expr(2) by auto 
            have "add (x, y) (\<tau> (x', y')) = (x*(fst (\<tau> (x', y'))),x*(snd (\<tau> (x', y'))))"
              by(simp add: z2)
            then have "add (x, y) (\<tau> (x', y')) = \<tau> (x*x',x*y')"
              apply(simp)
              apply(rule conjI)
              by(simp add: divide_simps t_nz cc x_expr \<open>x*x = 1\<close>)+
            then have v2_def: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) =
                          Some (\<tau> (x*x',x*y'), l+l'+1)"
              using v2 rot_com rotations_def by auto
            have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((x, 0), l), (x', y'), l'),
                   (((x, 0), l), \<tau> (x', y'), l' + 1)}) = 
                {(((x, 0), l), (x', y'), l'), (((x, 0), l), \<tau> (x', y'), l' + 1)}" 
              using v1_def v2_def z2 by auto
            have rho_aff: "(x * x', x * y') \<in> e_aff"
                using \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> unfolding e_aff_def e'_def
                apply(cases "x = 1")
                apply(simp)
                using x_expr by(simp add: z2)
            have eq: "{((x * x', x * y'), l + l'), (\<tau> (x * x', x * y'), l + l' + 1)}
                      = gluing `` {((x * x', x * y'), l + l')}"
            proof -
              have coord: "fst ((x * x', x * y')) \<noteq> 0" "snd ((x * x', x * y')) \<noteq> 0" 
                using x_expr cc by auto
              show ?thesis
                using gluing_class[OF coord(1) coord(2)] rho_aff by simp
            qed
            show ?thesis
              unfolding 2 apply(simp add: t_nz z2 del: \<tau>.simps)
              unfolding proj_add_class_def apply(simp add: dom_eq del: \<tau>.simps)
              apply(subst z2[symmetric])+
              apply(subst v1_def,subst v2_def,simp del: \<tau>.simps \<rho>.simps)
              apply(subst eq)   
              using eq_class_image rho_aff by fastforce
          next
            case z3
    
            consider
            (aaa) "p_delta ((x, y), l) (\<tau> (x', y'), l' + 1) \<noteq> 0 \<and> fst ((x, y), l)\<in> e_aff \<and> fst (\<tau> (x', y'), l' + 1) \<in> e_aff" |
            (bbb) "p_delta' ((x, y), l) (\<tau> (x', y'), l' + 1) \<noteq> 0 \<and> fst ((x, y), l) \<in> e_aff \<and> fst (\<tau> (x', y'), l' + 1) \<in> e_aff" |
            (ccc) "p_delta ((x, y), l) (\<tau> (x', y'), l' + 1) = 0 \<and> p_delta' ((x, y), l) (\<tau> (x', y'), l' + 1) = 0
                   \<or> fst ((x, y), l) \<notin> e_aff \<or> fst (\<tau> (x', y'), l' + 1) \<notin> e_aff" 
              by(simp add: proj_add.simps,blast) 
          then show ?thesis 
          proof(cases)
            case aaa
            
            from aaa have aaa_simp: 
              "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = 
               Some (add (x, y) (\<tau> (x', y')), l+l'+1)" 
              using proj_add.simps by simp
            have "x' * y' \<noteq> - x * y" 
              using aaa unfolding p_delta_def delta_def delta_plus_def delta_minus_def
              apply(simp add: t_nz cc divide_simps)
              apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1) d_nz)
              by(simp add: ring_distribs(1)[symmetric] d_nz)               
            have "x' * y' \<noteq> x * y"
              using aaa unfolding p_delta_def delta_def delta_plus_def delta_minus_def
              apply(simp add: t_nz cc divide_simps)
              by(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1))

            have closure_lem: "add (x, y) (\<tau> (x', y')) \<in> e_aff"
            proof -
              obtain x1 y1 where z2_d: "\<tau> (x', y') = (x1,y1)" by fastforce
              define z3 where "z3 = add (x,y) (x1,y1)"
              obtain x2 y2 where z3_d: "z3 = (x2,y2)" by fastforce
              have "delta x y x1 y1 \<noteq> 0"
                using aaa z2_d unfolding p_delta_def by auto
              then have dpm: "delta_minus x y x1 y1 \<noteq> 0" "delta_plus x y x1 y1 \<noteq> 0"
                unfolding delta_def by auto
              have "(x1,y1) \<in> e_aff"
                unfolding z2_d[symmetric]
                using \<open>\<tau> (x', y') \<in> e_aff\<close> by auto
              have e_eq: "e x y = 0" "e x1 y1 = 0"
                using \<open>(x,y) \<in> e_aff\<close> \<open>(x1,y1) \<in> e_aff\<close> e_e'_iff  unfolding e_aff_def by(auto)
                
              have "e x2 y2 = 0" 
                using add_closure[OF z3_d z3_def dpm ] 
                using add_closure[OF z3_d z3_def dpm e_eq] by simp
              then show ?thesis 
                unfolding e_aff_def using e_e'_iff z3_d z3_def z2_d by simp
            qed      

            have "
            fst (add (x,y) (\<tau> (x',y'))) = 0 \<or> 
            snd (add (x,y) (\<tau> (x',y'))) = 0 \<Longrightarrow>
            (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))"
            proof -
              define r1 where "r1 = fst(add (x,y) (\<tau> (x',y')))"
              define r2 where "r2 = snd(add (x,y) (\<tau> (x',y')))"
              from closure_lem have "(r1,r2) \<in> e_aff" using r1_def r2_def by simp
              assume "r1 = 0"              
              then have "r2 = 1 \<or> r2 = -1"
                using \<open>(r1,r2) \<in> e_aff\<close> unfolding e_aff_def e'_def 
                by(simp,algebra)  
              then obtain g where r_expr: "g \<in> rotations" "(r1,r2) = g (1,0)" 
                unfolding rotations_def using \<open>r1 = 0\<close> by force

              have e_eq: "e x y = 0"
                using \<open>(x,y) \<in> e_aff\<close> e_e'_iff unfolding e_aff_def by simp
              have d_eq: "delta_plus x y x y \<noteq> 0"
                  unfolding delta_plus_def
                  apply(subst (1) mult.assoc,subst (2) mult.assoc,subst (1) mult.assoc)
                  apply(subst power2_eq_square[symmetric])
                  using mult_nonneg_nonneg[OF c_d_pos zero_le_power2[of "x*y"]] by auto
              from r_expr have "add (x,y) (\<tau> (x',y')) = g (1,0)" 
                using r1_def r2_def by simp
              also have "... = g (add (x,y) (i (x,y)))"
                using inverse[OF e_eq d_eq] by fastforce
              also have "... = add (x,y) ((g \<circ> i) (x,y))"
                using \<open>g \<in> rotations\<close> unfolding rotations_def
                apply(auto)
                apply(simp add: c_eq_1)+
                apply(simp add: divide_simps)
                apply(simp add: c_eq_1)+
                by(simp add: algebra_simps divide_simps)
              finally have "add (x,y) (\<tau> (x',y')) = add (x,y) ((g \<circ> i) (x,y))"
                by blast
              then have "\<tau> (x',y') = (g \<circ> i) (x,y)"
              proof -  
                have "add (x,-y) (x,y) = (1,0)" 
                  using inverse[OF \<open>e x y = 0\<close> \<open>delta_plus x y x y \<noteq> 0\<close>] by fastforce
                then have "\<tau> (x',y') = add (add (x,-y) (x,y)) (\<tau> (x',y'))"
                  using neutral commutativity by simp
                also have "... = add (x,-y) (add (x,y) (\<tau> (x',y')))"
                  

              qed
                
            qed
              apply(simp add: divide_simps t_nz cc)
              apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1) d_nz \<open>x' * y' \<noteq> x * y\<close> t_nz)
              apply(simp add: c_eq_1)
              apply(simp add: ring_distribs(1)[symmetric] d_nz )
              apply(simp add: algebra_simps \<open>x' * y' \<noteq> - x * y\<close>)
          
              apply(safe)
            have "snd (add (x, y) (\<tau> (x', y'))) \<noteq> 0"
              apply(simp add: divide_simps t_nz cc)
              apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1) d_nz)
              apply(simp add: ring_distribs(1)[symmetric] d_nz) 
              apply(rule conjI)
              defer 1
              using \<open>x' * y' \<noteq> - x * y\<close> apply(simp)
              using \<open>\<tau> (x', y') \<in> e_aff\<close> \<open>(x,y) \<in> e_aff\<close> unfolding e_aff_def e'_def
              apply(simp)
              sorry
  
            have "fst (add (x, y) (\<tau> (x', y'))) \<noteq> 0"
              apply(simp add: divide_simps t_nz cc)
              apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1) d_nz c_eq_1)
              using aaa unfolding p_delta_def delta_def delta_plus_def delta_minus_def
              apply(simp add: t_nz cc \<open>x' * y' \<noteq> x * y\<close>)
              
             
            then show ?thesis sorry
          next
            case bbb
             "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = 
                   Some (ext_add (x, y) (\<tau> (x', y')), l+l'+1)"
            define arg where "arg = ext_add (x, y) (\<tau> (x', y'))"
            have "fst arg \<noteq> 0" 
              unfolding arg_def
              apply(simp add: divide_simps t_nz cc)
              apply(rule conjI)
              apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1))
              using d_nz unfolding delta_def delta_minus_def apply algebra
             
            have "gluing `` {(arg, l+l'+1)} = 
                  gluing `` {(\<tau> (arg), l+l')}"
              using gluing_inv[of  ] apply(simp) 
            then show ?thesis 
              sorry
          next
            case ccc
            have dom_eq: "(dom (\<lambda>(x, y). proj_add x y) \<inter>
                  {(((x, y), l), (x', y'), l'),(((x, y), l), \<tau> (x', y'), l' + 1)}) = 
                {(((x, y), l),((x', y'), l'))}" 
            using v1 ccc by auto
            then show ?thesis 
              unfolding 2 apply(simp add: cc t_nz del: \<tau>.simps)
              unfolding proj_add_class_def 
              apply(simp add: dom_eq del: \<tau>.simps)
              unfolding quotient_def by simp
          qed
            then show ?thesis sorry
          qed
        qed       
      next
        case c
        then show ?thesis sorry
      qed        
    next
      case 3
      then show ?thesis sorry
    next
      case 4
      then show ?thesis sorry
    qed
qed


end

end