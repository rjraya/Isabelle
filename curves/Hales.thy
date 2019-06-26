theory Hales
  imports Main
begin

context
  fixes c d :: int
begin      

fun e :: "int \<Rightarrow> int \<Rightarrow> int" where
 "e x y = x^2 + c * y^2 - 1 - d * x^2 * y^2"

fun delta_plus :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

fun delta_minus :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

fun delta :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * 
                      (delta_minus x1 y1 x2 y2)"

fun add :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
 "add z1 z2 = (case (z1,z2) of 
    ((x1,y1),(x2,y2)) \<Rightarrow>
    ((x1*x2 - c*y1*y2) div (1-d*x1*x2*y1*y2), 
     (x1*y2+y1*x2) div (1+d*x1*x2*y1*y2)))"

lemma add_with_deltas:
 "add z1 z2 = (case (z1,z2) of 
    ((x1,y1),(x2,y2)) \<Rightarrow>
    ((x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2), 
     (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2)))"
  by(cases "z1",cases "z2",simp add: algebra_simps)

theorem commutativity: "add z1 z2 = add z2 z1"
  by(cases "z1",cases "z2",simp add: algebra_simps)

(* try first with integers, in paper they use general rings *)
lemma e_squared: 
  assumes "x = r1 div a" "y = r2 div b"
  shows "\<exists> r. e x y = r div (a*b)^2"
  oops

lemma closure: 
  assumes "z1 = (x1,y1)" "z2 = (x2,y2)" "z3 = (x3,y3)" "z3 = add z1 z2"
  shows "e x1 y1 == 0 \<Longrightarrow> e x2 y2 == 0 \<Longrightarrow> 
         e x3 y3 == 0" 
proof -
  have x3_expr: "x3 = (x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2)"
    using assms add_with_deltas by auto
  have y3_expr: "y3 = (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2)"
    using assms add_with_deltas by auto
  obtain r where "(e x3 y3) * (delta x1 y1 x2 y2)^2 = r" by(simp)
  let ?e1 = "e x1 y1"
  let ?e2 = "e x2 y2"
  have "\<exists> r1 r2. r = r1 * ?e1 + r2 * ?e2"
    
    oops

end

end