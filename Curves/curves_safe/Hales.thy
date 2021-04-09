theory Hales
  imports  "HOL-Algebra.Group"  "HOL-Library.Bit" "HOL-Library.Rewrite"
begin

declare [[quick_and_dirty=true]]


section\<open>Affine Edwards curves\<close>

class ell_field = field + 
  assumes two_not_zero: "2 \<noteq> 0"

locale curve_addition =  
  fixes c d :: "'a::ell_field"
begin   

fun add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
 "add (x\<^sub>1,y\<^sub>1) (x\<^sub>2,y\<^sub>2) =
    ((x\<^sub>1*x\<^sub>2 - c*y\<^sub>1*y\<^sub>2) div (1-d*x\<^sub>1*y\<^sub>1*x\<^sub>2*y\<^sub>2), 
     (x\<^sub>1*y\<^sub>2+y\<^sub>1*x\<^sub>2) div (1+d*x\<^sub>1*y\<^sub>1*x\<^sub>2*y\<^sub>2))"

definition delta_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

definition delta_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

definition delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * 
                      (delta_minus x1 y1 x2 y2)"

definition e :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "e x y = x^2 + c * y^2 - 1 - d * x^2 * y^2"

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
  define g\<^sub>x where "g\<^sub>x = fst(add z1' (x3,y3)) - fst(add (x1,y1) z3')"
  define g\<^sub>y where "g\<^sub>y = snd(add z1' (x3,y3)) - snd(add (x1,y1) z3')"
  define gxpoly where "gxpoly = g\<^sub>x * Delta\<^sub>x"
  define gypoly where "gypoly = g\<^sub>y * Delta\<^sub>y"

  have x1'_expr: "x1' = (x1 * x2 - c * y1 * y2) / (1 - d * x1 * y1 * x2 * y2)"
    using assms(1,3) by simp
  have y1'_expr: "y1' = (x1 * y2 + y1 * x2) / (1 + d * x1 * y1 * x2 * y2)"
    using assms(1,3) by simp
  have x3'_expr: "x3' = (x2 * x3 - c * y2 * y3) / (1 - d * x2 * y2 * x3 * y3)"
    using assms(2,4) by simp
  have y3'_expr: "y3' = (x2 * y3 + y2 * x3) / (1 + d * x2 * y2 * x3 * y3)"
    using assms(2,4) by simp
  
  have non_unfolded_adds:
      "delta x1 y1 x2 y2 \<noteq> 0" using delta_def assms(5,6) by auto
  
  have simp1gx: "
    (x1' * x3 - c * y1' * y3) * delta_minus x1 y1 x3' y3' * 
    (delta x1 y1 x2 y2 * delta x2 y2 x3 y3) = 
      ((x1 * x2 - c * y1 * y2) * x3 * delta_plus x1 y1 x2 y2 - 
      c * (x1 * y2 + y1 * x2) * y3 * delta_minus x1 y1 x2 y2) *
      (delta_minus x2 y2 x3 y3 * delta_plus x2 y2 x3 y3 - 
      d * x1 * y1 * (x2 * x3 - c * y2 * y3) * (x2 * y3 + y2 * x3))
  "
    apply(rewrite x1'_expr y1'_expr x3'_expr y3'_expr)+
    apply(rewrite delta_minus_def)
    apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric] delta_plus_def[symmetric])+
    unfolding delta_def
    by(simp add: divide_simps assms(5-8))

  have simp2gx:
    "(x1 * x3' - c * y1 * y3') * delta_minus x1' y1' x3 y3 * 
     (delta x1 y1 x2 y2 * delta x2 y2 x3 y3) = 
       (x1 * (x2 * x3 - c * y2 * y3) * delta_plus x2 y2 x3 y3 - 
       c * y1 * (x2 * y3 + y2 * x3) * delta_minus x2 y2 x3 y3) *
       (delta_minus x1 y1 x2 y2 * delta_plus x1 y1 x2 y2 - 
       d * (x1 * x2 - c * y1 * y2) * (x1 * y2 + y1 * x2) * x3 * y3)"
    apply(rewrite x1'_expr y1'_expr x3'_expr y3'_expr)+
    apply(rewrite delta_minus_def)
    apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric] delta_plus_def[symmetric])+
    unfolding delta_def
    by(simp add: divide_simps assms(5-8))
  
  have "\<exists> r1 r2 r3. gxpoly = r1 * e1 + r2 * e2 + r3 * e3"
    unfolding gxpoly_def g\<^sub>x_def Delta\<^sub>x_def 
    apply(simp add: assms(1,2))
    apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric])+
    apply(simp add: divide_simps assms(9,11))
    apply(rewrite left_diff_distrib)
    apply(simp add: simp1gx simp2gx)
    unfolding delta_plus_def delta_minus_def
              e1_def e2_def e3_def e_def
    by algebra

  then show ?thesis
    sorry

qed

end



section\<open>Extension\<close>
(* Generalize for c \<noteq> 1 *)
locale ext_curve_addition = curve_addition +
  fixes t' :: "'a::ell_field"
  assumes c_eq_1: "c = 1"
  assumes t_intro: "d = t'^2"
  assumes t_ineq: "t'^2 \<noteq> 1" "t' \<noteq> 0"
begin

fun ext_add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
 "ext_add (x1,y1) (x2,y2) =
    ((x1*y1-x2*y2) div (x2*y1-x1*y2),
     (x1*y1+x2*y2) div (x1*x2+y1*y2))"

definition t where "t = t'" 

fun \<tau> :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where 
  "\<tau> (x,y) = (1/(t*x),1/(t*y))"




definition delta_x :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_x x1 y1 x2 y2 = x2*y1 - x1*y2"
definition delta_y :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_y x1 y1 x2 y2 = x1*x2 + y1*y2"
definition delta' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta' x1 y1 x2 y2 = delta_x x1 y1 x2 y2 * delta_y x1 y1 x2 y2"

definition e' where "e' x y = x^2 + y^2 - 1 - t^2 * x^2 * y^2"

definition "e'_aff = {(x,y). e' x y = 0}" 

definition gluing :: "((('a \<times> 'a) \<times> bit) \<times> (('a \<times> 'a) \<times> bit)) set" where
  "gluing = {(((x0,y0),l),((x1,y1),j)). 
               ((x0,y0) \<in> e'_aff \<and> (x1,y1) \<in> e'_aff) \<and>
               ((x0 \<noteq> 0 \<and> y0 \<noteq> 0 \<and> (x1,y1) = \<tau> (x0,y0) \<and> j = l+1) \<or>
                (x0 = x1 \<and> y0 = y1 \<and> l = j))}"


lemma coherence:
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "ext_add (x1,y1) (x2,y2) = add (x1,y1) (x2,y2)"
  sorry

type_synonym ('b) ppoint = \<open>(('b \<times> 'b) \<times> bit)\<close>

function proj_add :: "'a ppoint \<times>'a ppoint \<Rightarrow> 'a ppoint" where 
  "proj_add (((x\<^sub>1, y\<^sub>1), l),((x\<^sub>2, y\<^sub>2), j)) = (add (x\<^sub>1, y\<^sub>1) (x\<^sub>2, y\<^sub>2), l+j)"
 if "delta x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 \<noteq> 0 \<and> (x\<^sub>1, y\<^sub>1) \<in> e'_aff \<and> (x\<^sub>2, y\<^sub>2) \<in> e'_aff" 
| "proj_add (((x\<^sub>1, y\<^sub>1), l),((x\<^sub>2, y\<^sub>2), j)) = (ext_add (x\<^sub>1, y\<^sub>1) (x\<^sub>2, y\<^sub>2), l+j)"
 if "delta' x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 \<noteq> 0 \<and> (x\<^sub>1, y\<^sub>1) \<in> e'_aff \<and> (x\<^sub>2, y\<^sub>2) \<in> e'_aff"
  sorry

termination proj_add using "termination" by blast

definition e'_aff_0 where
  "e'_aff_0 = {((x\<^sub>1,y\<^sub>1),(x\<^sub>2,y\<^sub>2)). (x\<^sub>1,y\<^sub>1) \<in> e'_aff \<and> 
                                 (x\<^sub>2,y\<^sub>2) \<in> e'_aff \<and> 
                                 delta x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 \<noteq> 0 }"

definition e'_aff_1 where
  "e'_aff_1 = {((x\<^sub>1,y\<^sub>1),(x\<^sub>2,y\<^sub>2)). (x\<^sub>1,y\<^sub>1) \<in> e'_aff \<and> 
                                 (x\<^sub>2,y\<^sub>2) \<in> e'_aff \<and> 
                                 delta' x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 \<noteq> 0 }"

definition e'_aff_bit :: "(('a \<times> 'a) \<times> bit) set" where
 "e'_aff_bit = e'_aff \<times> UNIV"


definition e_proj where "e_proj = e'_aff_bit // gluing"


term "proj_add ` {(((x\<^sub>1, y\<^sub>1), i),((x\<^sub>2, y\<^sub>2), j)). 
                (((x\<^sub>1, y\<^sub>1), i),((x\<^sub>2, y\<^sub>2), j)) \<in> c\<^sub>1 \<times> c\<^sub>2 \<and> 
                ((x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)) \<in> e'_aff_0 \<union> e'_aff_1} "



term "{(((x\<^sub>1, y\<^sub>1), i),((x\<^sub>2, y\<^sub>2), j)). 
                (((x\<^sub>1, y\<^sub>1), i),((x\<^sub>2, y\<^sub>2), j)) \<in> c\<^sub>1 \<times> c\<^sub>2 \<and> 
                ((x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)) \<in> e'_aff_0 \<union> e'_aff_1} "

type_synonym ('b) pclass = \<open>('b) ppoint set\<close>

function proj_add_class :: "('a) pclass \<Rightarrow> ('a) pclass \<Rightarrow> ('a) pclass set"
where 
  "proj_add_class c\<^sub>1 c\<^sub>2 =       
        (proj_add ` {(((x\<^sub>1, y\<^sub>1), i),((x\<^sub>2, y\<^sub>2), j)). 
                (((x\<^sub>1, y\<^sub>1), i),((x\<^sub>2, y\<^sub>2), j)) \<in> c\<^sub>1 \<times> c\<^sub>2 \<and> 
                ((x\<^sub>1, y\<^sub>1), (x\<^sub>2, y\<^sub>2)) \<in> e'_aff_0 \<union> e'_aff_1}) // gluing
      " 
 if "c\<^sub>1 \<in> e_proj" and "c\<^sub>2 \<in> e_proj" 
  sorry

termination proj_add_class using "termination" by auto

definition proj_addition where 
  "proj_addition c\<^sub>1 c\<^sub>2 = the_elem (proj_add_class c\<^sub>1 c\<^sub>2)"





end

end
