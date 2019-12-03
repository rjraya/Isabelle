theory Hales
  imports  "HOL-Algebra.Group"  "HOL-Library.Bit" "HOL-Library.Rewrite"
begin

section\<open>Affine Edwards curves\<close>

class ell_field = field + 
  assumes two_not_zero: "2 \<noteq> 0"

locale curve_addition =  
  fixes c d :: "'a::ell_field"
begin   

fun add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - c*y1*y2) div (1-d*x1*y1*x2*y2), 
     (x1*y2+y1*x2) div (1+d*x1*y1*x2*y2))"

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

definition delta_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

definition delta_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

definition delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * 
                      (delta_minus x1 y1 x2 y2)"


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

function (domintros) proj_add :: "('a \<times> 'a) \<times> bit \<Rightarrow> ('a \<times> 'a) \<times> bit \<Rightarrow> ('a \<times> 'a) \<times> bit"
  where 
    "proj_add ((x1, y1), l) ((x2, y2), j) = (add (x1, y1) (x2, y2), l+j)"
   if "delta x1 y1 x2 y2 \<noteq> 0" and 
     "(x1, y1) \<in> e'_aff" and 
     "(x2, y2) \<in> e'_aff" 
  | "proj_add ((x1, y1), l) ((x2, y2), j) = (ext_add (x1, y1) (x2, y2), l+j)"
   if "delta' x1 y1 x2 y2 \<noteq> 0" and 
     "(x1, y1) \<in> e'_aff" and 
     "(x2, y2) \<in> e'_aff"
  | "proj_add ((x1, y1), l) ((x2, y2), j) = undefined" 
   if "(x1, y1) \<notin> e'_aff \<or> (x2, y2) \<notin> e'_aff \<or> 
        (delta x1 y1 x2 y2 = 0 \<and> delta' x1 y1 x2 y2 = 0)"
  apply(fast)
  apply(fastforce)
  using coherence e'_aff_def apply force
  by auto

termination proj_add using "termination" by blast

definition e'_aff_0 where
  "e'_aff_0 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e'_aff \<and> 
                                 (x2,y2) \<in> e'_aff \<and> 
                                 delta x1 y1 x2 y2 \<noteq> 0 }"

definition e'_aff_1 where
  "e'_aff_1 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e'_aff \<and> 
                                 (x2,y2) \<in> e'_aff \<and> 
                                 delta' x1 y1 x2 y2 \<noteq> 0 }"

definition e'_aff_bit :: "(('a \<times> 'a) \<times> bit) set" where
 "e'_aff_bit = e'_aff \<times> UNIV"

definition e_proj where "e_proj = e'_aff_bit // gluing"


function (domintros) proj_add_class :: "(('a \<times> 'a) \<times> bit ) set \<Rightarrow>
                                        (('a \<times> 'a) \<times> bit ) set \<Rightarrow> 
                                        ((('a \<times> 'a) \<times> bit ) set) set"
  where 
    "proj_add_class c1 c2 = 
        (
          {
            proj_add ((x1, y1), i) ((x2, y2), j) | 
              x1 y1 i x2 y2 j. 
              ((x1, y1), i) \<in> c1 \<and> 
              ((x2, y2), j) \<in> c2 \<and> 
              ((x1, y1), (x2, y2)) \<in> e'_aff_0 \<union> e'_aff_1
          } // gluing
        )" 
   if "c1 \<in> e_proj" and "c2 \<in> e_proj" 
  | "proj_add_class c1 c2 = undefined" 
   if "c1 \<notin> e_proj \<or> c2 \<notin> e_proj" 
  by (meson surj_pair) auto

termination proj_add_class using "termination" by auto

definition proj_addition where 
  "proj_addition c1 c2 = the_elem (proj_add_class c1 c2)"



end