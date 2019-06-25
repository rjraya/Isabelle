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
proof -
  have "e x y = 
        (r1 div a)\<^sup>2 + c * (r2 div b)\<^sup>2 - 1 -
        d * (r1 div a)\<^sup>2 * (r2 div b)\<^sup>2"
    by(simp add: assms)
  also have "... = 
        (r1^2 div a^2) + c * (r2 div b)\<^sup>2 - 1 -
        d * (r1 div a)\<^sup>2 * (r2 div b)\<^sup>2"
    
    apply(simp add: field_simps )
qed
  apply(simp add: assms)
  apply(simp add: field_simps)
  find_theorems "(_ div _)^_"

lemma closure: 
  assumes "z1 = (x1,y1)" "z2 = (x2,y2)" "z3 = (x3,y3)" "z3 = add z1 z2"
  shows "e x1 y1 == 0 \<Longrightarrow> e x2 y2 == 0 \<Longrightarrow> 
         e x3 y3 == 0" 
proof -
  have x3_expr: "x3 = (x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2)"
    using assms add_with_deltas by auto
  have y3_expr: "y3 = (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2)"
    using assms add_with_deltas by auto
  have "\<exists> r. e x3 y3 = r div (delta x1 y1 x2 y2)^2" 
    apply(simp)
    apply(simp add: x3_expr y3_expr) 
    apply(simp add: divide_simps)
qed

end

{e1, e2, e3} = {e[x1, y1], e[x2, y2], e[x3, y3]};

z0 = {x0,y0};
z1 = {x1,y1};
z2 = {x2,y2};
z3 = {x3,y3};

ez[{x_,y_}]:= e[x,y];
{e0,e1,e2,e3} = {ez[z0],ez[z1],ez[z2],ez[z3]};

fun delta where
 "delta x1 y1 x2 y2 = 1 - d^2*x1^2*x2^2*y1^2*y2^2"


end