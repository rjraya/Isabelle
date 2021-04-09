theory Hales_projective_independence
  imports  "HOL-Algebra.Group"  "HOL-Library.Bit" "HOL-Library.Rewrite"
begin

class ell_field = field +
  assumes two_not_zero: "2 \<noteq> 0"

section\<open>Extension\<close>

locale ext_curve_addition = 
  fixes t' d :: "'a::ell_field"
  assumes t_intro: "d = t'^2"
  assumes t_ineq: "t'^2 \<noteq> 1" "t' \<noteq> 0"
begin

subsection \<open>Change of variables\<close>

definition t where "t = t'"

lemma t_nz: "t \<noteq> 0" using t_ineq(2) t_def by auto

lemma d_nz: "d \<noteq> 0" using t_nz t_ineq t_intro by simp

lemma t_expr: "t^2 = d" "t^4 = d^2" using t_intro t_def by auto

lemma t_sq_n1: "t^2 \<noteq> 1"  using t_ineq(1) t_def by simp

lemma t_nm1: "t \<noteq> -1" using t_sq_n1 by fastforce

lemma d_n1: "d \<noteq> 1" using t_sq_n1 t_expr by blast

lemma t_n1: "t \<noteq> 1" using t_sq_n1 by fastforce

lemma t_dneq2: "2*t \<noteq> -2"
proof(rule ccontr)
  assume "\<not> 2 * t \<noteq> - 2"
  then have "2*t = -2" by auto
  then have "t = -1"
    using two_not_zero mult_cancel_left by fastforce
  then show "False"
    using t_nm1 by argo
qed

subsection \<open>New points\<close>

definition e where "e x y = x^2 + y^2 - 1 - t^2 * x^2 * y^2"

definition delta_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

definition delta_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

definition delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * (delta_minus x1 y1 x2 y2)"

lemma delta_com: "(delta x0 y0 x1 y1 = 0) = (delta x1 y1 x0 y0 = 0)"
  unfolding delta_def delta_minus_def delta_plus_def 
  by algebra

definition "e_aff = {p. e (fst p) (snd p) = 0}"
definition "e_circ = {p. fst p \<noteq> 0 \<and> snd p \<noteq> 0 \<and> p \<in> e_aff}"

fun add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" (infix "\<oplus>\<^sub>0" 600) where
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - y1*y2) div (1-d*x1*y1*x2*y2), 
     (x1*y2+y1*x2) div (1+d*x1*y1*x2*y2))"

lemma add_neutral: "add z (1,0) = z" by(cases "z",simp)

lemma add_comm: "add z1 z2 = add z2 z1"
  by(cases "z1",cases "z2",simp add: algebra_simps)

lemma add_closure:
  assumes "delta x y x' y' \<noteq> 0" "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"
  shows "add (x,y) (x',y') \<in> e_aff"
  using assms
  unfolding delta_def delta_plus_def delta_minus_def e_aff_def e_def
  apply(simp add: divide_simps t_expr)
  by algebra

lemma circ_to_aff: "p \<in> e_circ \<Longrightarrow> p \<in> e_aff"
  unfolding e_circ_def by auto

subsection \<open>Group transformations and inversions\<close>

fun \<rho> :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where  "\<rho> (x,y) = (-y,x)"
fun \<tau> :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where "\<tau> (x,y) = (1/(t*x),1/(t*y))"

definition G where
  "G \<equiv> {id,\<rho>,\<rho> \<circ> \<rho>,\<rho> \<circ> \<rho> \<circ> \<rho>,\<tau>,\<tau> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>}"

definition rotations where
  "rotations = {id,\<rho>,\<rho> \<circ> \<rho>,\<rho> \<circ> \<rho> \<circ> \<rho>}"

definition symmetries where
  "symmetries = {\<tau>,\<tau> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>}"

lemma G_partition: "G = rotations \<union> symmetries"
  unfolding G_def rotations_def symmetries_def by fastforce

subsubsection \<open>Rotations\<close>


subsubsection \<open>Symmetries\<close>

(* See if we can remove this and leave only tau_idemps *)
lemma tau_sq: "(\<tau> \<circ> \<tau>) (x,y) = (x,y)" by(simp add: t_nz)

lemma tau_idemp: "\<tau> \<circ> \<tau> = id"
  using t_nz comp_def by auto 

lemma tau_idemp_explicit: "\<tau>(\<tau>(x,y)) = (x,y)"
  using tau_idemp pointfree_idE by fast

lemma tau_idemp_point: "\<tau>(\<tau> p) = p"
  using o_apply[symmetric, of \<tau> \<tau> p] tau_idemp by simp  

subsection \<open>Point inverse\<close>

fun i :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where 
  "i (a,b) = (a,-b)" 

lemma i_idemp: "i \<circ> i = id"
  using comp_def by auto

lemma i_idemp_explicit: "i(i(x,y)) = (x,y)"
  using i_idemp pointfree_idE by fast

lemma i_aff:
  assumes "p \<in> e_aff"
  shows "i p \<in> e_aff"
  using assms unfolding e_aff_def e_def by(cases "p",simp)

lemma i_circ:
  assumes "(x,y) \<in> e_circ"
  shows "i (x,y) \<in> e_circ"
  using assms unfolding e_circ_def e_aff_def e_def by auto

lemma i_circ_points:
  assumes "p \<in> e_circ"
  shows "i p \<in> e_circ"
  using assms unfolding e_circ_def e_aff_def e_def by(cases "p",simp)

subsection \<open>Something else\<close>

lemma tau_rot_sym:
  assumes "r \<in> rotations"
  shows "\<tau> \<circ> r \<in> symmetries"
  using assms unfolding rotations_def symmetries_def by auto

lemma tau_rho_com:
  "\<tau> \<circ> \<rho> = \<rho> \<circ> \<tau>" by auto

lemma tau_rot_com:
  assumes "r \<in> rotations"
  shows "\<tau> \<circ> r = r \<circ> \<tau>"
  using assms unfolding rotations_def by fastforce

lemma rho_order_4:
  "\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho> = id" by auto
  
lemma rho_i_com_inverses:
  "i (id (x,y)) = id (i (x,y))"
  "i (\<rho> (x,y)) = (\<rho> \<circ> \<rho> \<circ> \<rho>) (i (x,y))"
  "i ((\<rho> \<circ> \<rho>) (x,y)) = (\<rho> \<circ> \<rho>) (i (x,y))"
  "i ((\<rho> \<circ> \<rho> \<circ> \<rho>) (x,y)) = \<rho> (i (x,y))"
  by(simp)+

lemma rotations_i_inverse:
  assumes "tr \<in> rotations"
  shows "\<exists> tr' \<in> rotations. (tr \<circ> i) p = (i \<circ> tr') p \<and> tr \<circ> tr' = id"
  using assms rho_i_com_inverses unfolding rotations_def
  by(cases "p",simp,elim disjE,auto)

lemma tau_i_com_inverses:
  "(i \<circ> \<tau>) (x,y) = (\<tau> \<circ> i) (x,y)"
  "(i \<circ> \<tau> \<circ> \<rho>) (x,y) = (\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) (x,y)"
  "(i \<circ> \<tau> \<circ> \<rho> \<circ> \<rho>) (x,y) = (\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> i) (x,y)"
  "(i \<circ> \<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>) (x,y) = (\<tau> \<circ> \<rho> \<circ> i) (x,y)"
  by(simp)+

lemma rho_circ: 
  assumes "p \<in> e_circ"
  shows "\<rho> p \<in> e_circ"
  using assms unfolding e_circ_def e_aff_def e_def 
  by(cases "p",simp split: prod.splits add: add.commute)



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
  using assms unfolding e_circ_def e_aff_def e_def
  apply(simp split: prod.splits) 
  by(cases "p", simp add: divide_simps t_nz power2_eq_square algebra_simps)

lemma rot_comp:
  assumes "t1 \<in> rotations" "t2 \<in> rotations"
  shows "t1 \<circ> t2 \<in> rotations"
  using assms unfolding rotations_def by auto

lemma rot_tau_com:
  assumes "tr \<in> rotations"
  shows "tr \<circ> \<tau> = \<tau> \<circ> tr"
  using assms unfolding rotations_def by(auto)

lemma tau_i_com: "\<tau> \<circ> i = i \<circ> \<tau>" by auto

lemma rot_com:
  assumes "r \<in> rotations" "r' \<in> rotations"
  shows "r' \<circ> r = r \<circ> r'" 
  using assms unfolding rotations_def by force

lemma rot_inv:
  assumes "r \<in> rotations"
  shows "\<exists> r' \<in> rotations. r' \<circ> r = id" 
  using assms unfolding rotations_def by force

lemma rot_aff:
  assumes "r \<in> rotations" "p \<in> e_aff"
  shows "r p \<in> e_aff"
  using assms unfolding rotations_def e_aff_def e_def
  by(cases "p",auto simp add: semiring_normalization_rules(16) add.commute)

lemma tau_not_id: "\<tau> \<noteq> id"
  apply(simp add: fun_eq_iff) 
  apply(simp add: divide_simps t_nz) 
  apply(simp add: field_simps) 
  by (metis mult.left_neutral t_n1 zero_neq_one)

lemma sym_not_id:
  assumes "r \<in> rotations"
  shows "\<tau> \<circ> r \<noteq> id"
  using assms unfolding rotations_def 
  apply(subst fun_eq_iff,simp)
  apply(auto)
  using tau_not_id apply auto[1]
    apply (metis d_nz)
   apply(simp add: divide_simps t_nz)
  apply(simp add: field_simps)
   apply (metis mult_numeral_1 numeral_One one_neq_zero 
                power2_minus power_one t_sq_n1)
  by (metis d_nz)

lemma sym_decomp:
  assumes "g \<in> symmetries"
  shows "\<exists> r \<in> rotations. g = \<tau> \<circ> r"
  using assms unfolding symmetries_def rotations_def by auto

lemma symmetries_i_inverse:
  assumes "tr \<in> symmetries"
  shows "\<exists> tr' \<in> symmetries. (tr \<circ> i) (x,y) = (i \<circ> tr') (x,y) \<and> tr \<circ> tr' = id"
proof -
  consider (1) "tr = \<tau>" | 
           (2) "tr = \<tau> \<circ> \<rho>" | 
           (3) "tr = \<tau> \<circ> \<rho> \<circ> \<rho>" | 
           (4) "tr = \<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>" 
    using assms unfolding symmetries_def by blast
  then show ?thesis
  proof(cases)
    case 1
    define tr' where "tr' = \<tau>" 
    have "(tr \<circ> i) (x, y) = (i \<circ> tr') (x, y) \<and> tr \<circ> tr' = id" "tr' \<in> symmetries"
      using tr'_def 1 tau_idemp symmetries_def by simp+      
    then show ?thesis by blast
  next
    case 2
    define tr' where "tr' = \<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>" 
    have "(tr \<circ> i) (x, y) = (i \<circ> tr') (x, y) \<and> tr \<circ> tr' = id" "tr' \<in> symmetries"
      using tr'_def 2 
      apply(simp)
      apply(metis (no_types, hide_lams) comp_id fun.map_comp rho_order_4 tau_idemp tau_rho_com)
      using symmetries_def tr'_def by simp
    then show ?thesis by blast
  next
    case 3
    define tr' where "tr' = \<tau> \<circ> \<rho> \<circ> \<rho>" 
    have "(tr \<circ> i) (x, y) = (i \<circ> tr') (x, y) \<and> tr \<circ> tr' = id" "tr' \<in> symmetries"
      using tr'_def 3
      apply(simp)
      apply(metis (no_types, hide_lams) comp_id fun.map_comp rho_order_4 tau_idemp tau_rho_com)
      using symmetries_def tr'_def by simp
    then show ?thesis by blast
  next
    case 4
    define tr' where "tr' = \<tau> \<circ> \<rho>" 
    have "(tr \<circ> i) (x, y) = (i \<circ> tr') (x, y) \<and> tr \<circ> tr' = id" "tr' \<in> symmetries"
      using tr'_def 4
      apply(simp)
      apply(metis (no_types, hide_lams) comp_id fun.map_comp rho_order_4 tau_idemp tau_rho_com)
      using symmetries_def tr'_def by simp
    then show ?thesis by blast
  qed
qed

lemma sym_to_rot: "g \<in> symmetries \<Longrightarrow> \<tau> \<circ> g \<in> rotations"
  using tau_idemp unfolding symmetries_def rotations_def
  apply(simp)
  apply(elim disjE)
  apply fast
  by(simp add: fun.map_comp)+

subsection \<open>Extended addition\<close>

fun ext_add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" (infix "\<oplus>\<^sub>1" 600) where
 "ext_add (x1,y1) (x2,y2) =
    ((x1*y1-x2*y2) div (x2*y1-x1*y2),
     (x1*y1+x2*y2) div (x1*x2+y1*y2))"

definition delta_x :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_x x1 y1 x2 y2 = x2*y1 - x1*y2"
definition delta_y :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_y x1 y1 x2 y2 = x1*x2 + y1*y2"
definition delta' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta' x1 y1 x2 y2 = delta_x x1 y1 x2 y2 * delta_y x1 y1 x2 y2"

lemma delta'_com: "(delta' x0 y0 x1 y1 = 0) = (delta' x1 y1 x0 y0 = 0)"
  unfolding delta'_def delta_x_def delta_y_def 
  by algebra

definition e_aff_0 where
  "e_aff_0 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e_aff \<and> 
                                 (x2,y2) \<in> e_aff \<and> 
                                 delta x1 y1 x2 y2 \<noteq> 0 }"

definition e_aff_1 where
  "e_aff_1 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e_aff \<and> 
                                 (x2,y2) \<in> e_aff \<and> 
                                 delta' x1 y1 x2 y2 \<noteq> 0 }"

lemma ext_add_comm:
  "ext_add z1 z2 = ext_add z2 z1"
proof -
  obtain x1 y1 x2 y2 where z_expr: "z1 = (x1,y1)" "z2 = (x2,y2)" 
    using surj_pair by force
  have "ext_add (x1,y1) (x2,y2) = ext_add (x2,y2) (x1,y1)"
    by(simp add: divide_simps,algebra)
  then show ?thesis
    using z_expr by auto
qed

lemma ext_add_inverse:
  assumes "(fst p) \<noteq> 0" "(snd p) \<noteq> 0"
  shows "ext_add p (i p) = (1,0)"
proof - 
  obtain x y where p_expr: "p = (x,y)" 
    using surj_pair by fastforce
  then have "ext_add (x,y) (i (x,y)) = (1,0)" 
    using assms by(simp add: two_not_zero)
  then show ?thesis
    using p_expr by auto
qed

lemma ext_add_neutral:
  assumes "fst p \<noteq> 0" "snd p \<noteq> 0"
  shows "ext_add p (1,0) = p"
  using assms by(cases "p",force) 

subsubsection \<open>Inversion and rotation invariance\<close>

lemma inversion_invariance_1:
  assumes "fst p1 \<noteq> 0" "snd p1 \<noteq> 0" "fst p2 \<noteq> 0" "snd p2 \<noteq> 0" 
  shows "add (\<tau> p1) p2 = add p1 (\<tau> p2)"
  using assms
  apply(cases "p1",cases "p2")
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz d_nz)
  by(simp_all add: algebra_simps)

lemma inversion_invariance_2:
  assumes "fst p1 \<noteq> 0" "snd p1 \<noteq> 0" "fst p2 \<noteq> 0" "snd p2 \<noteq> 0" 
  shows "ext_add (\<tau> p1) p2 = ext_add p1 (\<tau> p2)"
  using assms
  apply(cases "p1", cases "p2")
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz d_nz)
  by(simp_all add: algebra_simps)

lemma rho_invariance_1:
  "add (\<rho> p1) p2 = \<rho> (add p1 p2)"
  apply(cases "p1",cases "p2")
  apply(simp)
  by(simp add: algebra_simps divide_simps)

lemma rotation_invariance_1: 
  assumes "r \<in> rotations"
  shows "add (r p1) p2 = r (add p1 p2)"
  apply(cases "p1",cases "p2")
  using rho_invariance_1 assms unfolding rotations_def
  apply(safe)
  apply(simp,simp) 
  by(metis comp_apply prod.exhaust_sel)+

lemma rho_invariance_2:
  "ext_add (\<rho> p1) p2 = \<rho> (ext_add p1 p2)"
  apply(cases "p1",cases "p2")
  by(simp add: algebra_simps divide_simps)

lemma rotation_invariance_2: 
  assumes "r \<in> rotations"
  shows "ext_add (r p1) p2 = r (ext_add p1 p2)"
  apply(cases "p1",cases "p2")
  using rho_invariance_2 assms unfolding rotations_def
  apply(safe)
  apply(simp,simp) 
  by(metis comp_apply prod.exhaust_sel)+

lemma rotation_invariance_3: 
  "delta x1 y1 (fst (\<rho> (x2,y2))) (snd (\<rho> (x2,y2))) = 
   delta x1 y1 x2 y2"
  by(simp add: delta_def delta_plus_def delta_minus_def,algebra)

lemma rotation_invariance_4: 
  "delta' x1 y1 (fst (\<rho> (x2,y2))) (snd (\<rho> (x2,y2))) = - delta' x1 y1 x2 y2"
  by(simp add: delta'_def delta_x_def delta_y_def,algebra)

lemma inverse_rule_1:
  "(\<tau> \<circ> i \<circ> \<tau>) (x,y) = i (x,y)" by (simp add: t_nz)
lemma inverse_rule_2:
  "(\<rho> \<circ> i \<circ> \<rho>) (x,y) = i (x,y)" by simp
lemma inverse_rule_3:
  "i (add p1 p2) = add (i p1) (i p2)"
  by(cases "p1",cases "p2",simp add: divide_simps)
lemma inverse_rule_4:
  "i (ext_add p1 p2) = ext_add (i p1) (i p2)"
  by(cases "p1",cases "p2",simp add: algebra_simps divide_simps)

lemma e_aff_x0:
  assumes "x = 0" "(x,y) \<in> e_aff"
  shows "y = 1 \<or> y = -1"
  using assms unfolding e_aff_def e_def
  by(simp,algebra)

lemma e_aff_y0:
  assumes "y = 0" "(x,y) \<in> e_aff"
  shows "x = 1 \<or> x = -1"
  using assms unfolding e_aff_def e_def
  by(simp,algebra) 

lemma add_ext_add:
  assumes "fst p1 \<noteq> 0" "snd p1 \<noteq> 0" 
  shows "ext_add p1 p2 = \<tau> (add (\<tau> p1) p2)"
  using assms
  apply(cases "p1", cases "p2")
  apply(simp)
  apply(rule conjI)
  apply(simp add: divide_simps t_nz power2_eq_square[symmetric] assms t_expr(1) d_nz)
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1)) 
  apply (simp add: semiring_normalization_rules(18) semiring_normalization_rules(29) t_intro)
  apply(simp add: divide_simps t_nz power2_eq_square[symmetric] assms t_expr(1) d_nz)
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1))  
  by (simp add: power2_eq_square t_intro)

corollary add_ext_add_2:
  assumes "fst p1 \<noteq> 0" "snd p1 \<noteq> 0" 
  shows "add p1 p2 = \<tau> (ext_add (\<tau> p1) p2)"
proof -
  obtain x1 y1 x2 y2  where p_expr: "p1 = (x1,y1)" "p2 = (x2,y2)"
    using surj_pair by fastforce
  obtain x1' y1' where tau_expr: "\<tau> (x1,y1) = (x1',y1')" by simp
  then have p_nz: "x1' \<noteq> 0" "y1' \<noteq> 0" 
    using assms(1) tau_idemp_point apply auto[1]
    using \<open>\<tau> (x1, y1) = (x1', y1')\<close> assms(2) tau_sq p_expr by auto
  have "add (x1,y1) (x2,y2) = add (\<tau> (x1', y1')) (x2, y2)"
    using tau_expr tau_idemp 
    by (metis comp_apply id_apply)
  also have "... = \<tau> (ext_add (x1', y1') (x2, y2))"
    using add_ext_add p_nz tau_idemp by force
  also have "... = \<tau> (ext_add (\<tau> (x1, y1)) (x2, y2))"
    using tau_expr tau_idemp by auto
  finally show ?thesis using p_expr by blast
qed

subsubsection \<open>Coherence and closure\<close>

lemma coherence_1:
  assumes "delta_x x1 y1 x2 y2 \<noteq> 0" "delta_minus x1 y1 x2 y2 \<noteq> 0" 
  assumes "e x1 y1 = 0" "e x2 y2 = 0"
  shows "delta_x x1 y1 x2 y2 * delta_minus x1 y1 x2 y2 *
         (fst (ext_add (x1,y1) (x2,y2)) - fst (add (x1,y1) (x2,y2)))
         = x2 * y2 * e x1 y1 - x1 * y1 * e x2 y2"
  apply(simp)  
  apply(rewrite in "_ / \<hole>" delta_x_def[symmetric])
  apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric])
  apply(simp add: assms(1,2) divide_simps)
  unfolding delta_minus_def delta_x_def e_def
  apply(simp add: t_expr)
  by(simp add: power2_eq_square field_simps)  
  
lemma coherence_2:
  assumes "delta_y x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0" 
  assumes "e x1 y1 = 0" "e x2 y2 = 0"
  shows "delta_y x1 y1 x2 y2 * delta_plus x1 y1 x2 y2 *
         (snd (ext_add (x1,y1) (x2,y2)) - snd (add (x1,y1) (x2,y2)))
         = - x2 * y2 * e x1 y1 - x1 * y1 * e x2 y2"
  apply(simp)  
  apply(rewrite in "_ / \<hole>" delta_y_def[symmetric])
  apply(rewrite in "_ / \<hole>" delta_plus_def[symmetric])
  apply(simp add: assms(1,2) divide_simps)
  unfolding delta_plus_def delta_y_def e_def
  apply(subst t_expr)+
  by(simp add: power2_eq_square  field_simps)
  
lemma coherence:
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes "e x1 y1 = 0" "e x2 y2 = 0"
  shows "ext_add (x1,y1) (x2,y2) = add (x1,y1) (x2,y2)"
  using coherence_1 coherence_2 delta_def delta'_def assms by auto

lemma ext_add_closure:
  assumes "delta' x1 y1 x2 y2 \<noteq> 0"
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" 
  shows "ext_add (x1,y1) (x2,y2) \<in> e_aff"
  using assms 
  unfolding e_aff_def e_def delta'_def delta_x_def delta_y_def
  apply(simp add: divide_simps t_expr)
  by algebra

subsubsection \<open>Useful lemmas in the extension\<close>

lemma inverse_generalized:
  assumes "(a,b) \<in> e_aff" "delta_plus a b a b \<noteq> 0"
  shows "add (a,b) (i (a,b)) = (1,0)" 
  using assms
  unfolding delta_plus_def e_aff_def e_def
  apply(simp add: t_expr)
  by algebra

lemma add_self:
  assumes in_aff: "(x,y) \<in> e_aff"
  shows "delta x y x (-y) \<noteq> 0 \<or> delta' x y x (-y) \<noteq> 0 "
    using in_aff d_n1 
    unfolding delta_def delta_plus_def delta_minus_def
              delta'_def delta_x_def delta_y_def
              e_aff_def e_def
    apply(simp add: t_expr two_not_zero)
    apply(safe)
    apply(simp_all add: algebra_simps) 
    by(simp add: semiring_normalization_rules(18) semiring_normalization_rules(29) two_not_zero)+

subsection \<open>Delta arithmetic\<close>

lemma mix_tau:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "x2 \<noteq> 0" "y2 \<noteq> 0"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e_aff_def e_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_nz algebra_simps)
  apply(simp add: power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz)
  by algebra

lemma mix_tau_0:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "x2 \<noteq> 0" "y2 \<noteq> 0"
  assumes "delta x1 y1 x2 y2 = 0"
  shows "delta' x1 y1 x2 y2 = 0 \<or> delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0" 
  using assms
  unfolding e_aff_def e_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_nz algebra_simps)
  apply(simp add: power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz)
  by algebra

lemma mix_tau_prime:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "x2 \<noteq> 0" "y2 \<noteq> 0"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta' x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e_aff_def e_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_nz algebra_simps)
  apply(simp add: power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz)
  by algebra

lemma tau_tau_d:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" 
  assumes "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e_aff_def e_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_expr)
  apply(simp split: if_splits add: divide_simps t_nz)
  apply(simp_all add: t_nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply algebra
  by algebra

lemma tau_tau_d':
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" 
  assumes "delta' (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta' x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e_aff_def e_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_expr)
  apply(simp split: if_splits add: divide_simps t_nz) 
  apply fastforce
  apply algebra
  by algebra

lemma delta_add_delta'_1: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes r_expr: "rx = fst (add (x1,y1) (x2,y2))" "ry = snd (add (x1,y1) (x2,y2))" 
  assumes in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
  assumes pd: "delta x1 y1 x2 y2 \<noteq> 0" 
  assumes pd': "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  using pd in_aff unfolding r_expr delta_def delta_minus_def delta_plus_def
                            e_aff_def e_def
  apply(simp add: divide_simps t_expr)
  apply(simp add: algebra_simps)
  by algebra

lemma delta'_add_delta_1: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes r_expr: "rx = fst (ext_add (x1,y1) (x2,y2))" "ry = snd (ext_add (x1,y1) (x2,y2))" 
  assumes in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
  assumes pd': "delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  using in_aff unfolding r_expr delta_def delta_minus_def delta_plus_def
                            e_aff_def e_def
  apply(simp split: if_splits add: divide_simps t_expr)
  apply(simp add: algebra_simps)
  by algebra

(* These lemmas are needed in the general field setting. 
   Funnily enough, if we drop assumptions the goal is proven, but 
   with more assumptions as in delta_add_delta', is not*)
lemma funny_field_lemma_1: 
  "((x1 * x2 - y1 * y2) * ((x1 * x2 - y1 * y2) * (x2 * (y2 * (1 + d * x1 * y1 * x2 * y2)))) +
     (x1 * x2 - y1 * y2) * ((x1 * y2 + y1 * x2) * y2\<^sup>2) * (1 - d * x1 * y1 * x2 * y2)) *
    (1 + d * x1 * y1 * x2 * y2) \<noteq>
    ((x1 * y2 + y1 * x2) * ((x1 * y2 + y1 * x2) * (x2 * (y2 * (1 - d * x1 * y1 * x2 * y2)))) +
     (x1 * x2 - y1 * y2) * ((x1 * y2 + y1 * x2) * x2\<^sup>2) * (1 + d * x1 * y1 * x2 * y2)) *
    (1 - d * x1 * y1 * x2 * y2) \<Longrightarrow>
    (d * ((x1 * x2 - y1 * y2) * ((x1 * y2 + y1 * x2) * (x2 * y2))))\<^sup>2 =
    ((1 - d * x1 * y1 * x2 * y2) * (1 + d * x1 * y1 * x2 * y2))\<^sup>2 \<Longrightarrow>
    x1\<^sup>2 + y1\<^sup>2 - 1 = d * x1\<^sup>2 * y1\<^sup>2 \<Longrightarrow>
    x2\<^sup>2 + y2\<^sup>2 - 1 = d * x2\<^sup>2 * y2\<^sup>2  \<Longrightarrow> False"
  by algebra
  

lemma delta_add_delta'_2: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes r_expr: "rx = fst (add (x1,y1) (x2,y2))" "ry = snd (add (x1,y1) (x2,y2))" 
  assumes in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
  assumes pd: "delta x1 y1 x2 y2 \<noteq> 0" 
  assumes pd': "delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0" 
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply safe
  using pd unfolding r_expr delta_def delta_minus_def delta_plus_def
  apply(simp)
  apply(simp add: divide_simps)
  using in_aff unfolding e_aff_def e_def
  apply(simp add: t_expr)
  apply safe   
  using funny_field_lemma_1 by blast


(* These lemmas are needed in the general field setting. 
   Funnily enough, if we drop assumptions the goal is proven, but 
   with more assumptions as in delta_add_delta', is not*)
lemma funny_field_lemma_2: " (x2 * y2)\<^sup>2 * ((x2 * y1 - x1 * y2) * (x1 * x2 + y1 * y2))\<^sup>2 \<noteq> ((x1 * y1 - x2 * y2) * (x1 * y1 + x2 * y2))\<^sup>2 \<Longrightarrow>
    ((x1 * y1 - x2 * y2) * ((x1 * y1 - x2 * y2) * (x2 * (y2 * (x1 * x2 + y1 * y2)))) +
     (x1 * y1 - x2 * y2) * ((x1 * y1 + x2 * y2) * x2\<^sup>2) * (x2 * y1 - x1 * y2)) *
    (x1 * x2 + y1 * y2) =
    ((x1 * y1 + x2 * y2) * ((x1 * y1 + x2 * y2) * (x2 * (y2 * (x2 * y1 - x1 * y2)))) +
     (x1 * y1 - x2 * y2) * ((x1 * y1 + x2 * y2) * y2\<^sup>2) * (x1 * x2 + y1 * y2)) *
    (x2 * y1 - x1 * y2) \<Longrightarrow>
    x1\<^sup>2 + y1\<^sup>2 - 1 = d * x1\<^sup>2 * y1\<^sup>2 \<Longrightarrow>
    x2\<^sup>2 + y2\<^sup>2 - 1 = d * x2\<^sup>2 * y2\<^sup>2 \<Longrightarrow> False"
  by algebra

lemma delta'_add_delta_2: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes r_expr: "rx = fst (ext_add (x1,y1) (x2,y2))" "ry = snd (ext_add (x1,y1) (x2,y2))" 
  assumes in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
  assumes pd: "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes pd': "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply safe
  using pd unfolding r_expr delta'_def delta_x_def delta_y_def
  apply(simp)
  apply(simp split: if_splits add: divide_simps)
  using in_aff unfolding e_aff_def e_def
  apply(simp add: t_expr)
  apply safe  
  using funny_field_lemma_2 by fast

lemma delta'_add_delta_not_add: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
  assumes pd: "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes add_nz: "fst (ext_add (x1,y1) (x2,y2)) \<noteq> 0"  "snd (ext_add (x1,y1) (x2,y2)) \<noteq> 0"
  shows pd': "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) x2 y2 \<noteq> 0"
  using add_ext_add[OF ] 1 in_aff
  using pd 1  unfolding delta_def delta_minus_def delta_plus_def
                        delta'_def delta_x_def delta_y_def 
                     e_aff_def e_def
  apply(simp add: divide_simps t_nz)
   apply(simp_all split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  using add_nz
  apply(simp add: d_nz) 
  using d_nz 
  by (metis distrib_left mult_eq_0_iff)

lemma not_add_self:
  assumes in_aff: "(x,y) \<in> e_aff" "x \<noteq> 0" "y \<noteq> 0" 
  shows "delta x y (fst (\<tau> (i (x,y)))) (snd (\<tau> (i (x,y)))) = 0"
        "delta' x y (fst (\<tau> (i (x,y)))) (snd (\<tau> (i (x,y)))) = 0"
    using in_aff d_n1 
    unfolding delta_def delta_plus_def delta_minus_def
              delta'_def delta_x_def delta_y_def
              e_aff_def e_def
    apply(simp add: t_expr two_not_zero)
    apply(safe)
    by(simp_all add: algebra_simps t_nz power2_eq_square[symmetric] t_expr) 

section \<open>Projective Edwards curves\<close>

subsection \<open>No fixed-point lemma and dichotomies\<close>

lemma g_no_fp:
  assumes "g \<in> G" "p \<in> e_circ" "g p = p" 
  shows "g = id"
proof -
  obtain x y where p_def: "p = (x,y)" by fastforce
  have nz: "x \<noteq> 0" "y \<noteq> 0" using assms p_def  unfolding e_circ_def by auto

  consider (id) "g = id" | (rot) "g \<in> rotations" "g \<noteq> id" | (sym) "g \<in> symmetries" "g \<noteq> id"
    using G_partition assms by blast
  then show ?thesis
  proof(cases)
    case id then show ?thesis by simp
  next 
    case rot
    then have "x = 0"  
      using assms(3) two_not_zero
      unfolding rotations_def p_def  
      by auto
    then have "False" 
      using nz by blast
    then show ?thesis by blast
  next
    case sym
    then have "t*x*y = 0 \<or> (t*x^2 \<in> {-1,1} \<and> t*y^2 \<in> {-1,1} \<and> t*x^2 = t*y^2)"
      using assms(3) two_not_zero
      unfolding symmetries_def p_def power2_eq_square
      apply(safe) 
      apply(auto simp add: algebra_simps divide_simps two_not_zero)
      using two_not_zero by metis+
    then have "e x y = 2 * (1 - t) / t \<or> e x y = 2 * (-1 - t) / t"
      using nz t_nz unfolding e_def 
      by(simp add: algebra_simps divide_simps,algebra)
    then have "e x y \<noteq> 0" 
      using t_dneq2 t_n1
      by(auto simp add: algebra_simps divide_simps t_nz) 
    then have "False"
      using assms nz p_def unfolding e_circ_def e_aff_def by fastforce
    then show ?thesis by simp
  qed
qed

lemma dichotomy_1:
  assumes "p \<in> e_aff" "q \<in> e_aff" 
  shows "(p \<in> e_circ \<and> (\<exists> g \<in> symmetries. q = (g \<circ> i) p)) \<or> 
         (p,q) \<in> e_aff_0 \<or> (p,q) \<in> e_aff_1" 
proof -
  obtain x1 y1 where p_def: "p = (x1,y1)" by fastforce
  obtain x2 y2 where q_def: "q = (x2,y2)" by fastforce
  
  consider (1) "(p,q) \<in> e_aff_0" |
           (2) "(p,q) \<in> e_aff_1" |
           (3) "(p,q) \<notin> e_aff_0 \<and> (p,q) \<notin> e_aff_1" by blast
  then show ?thesis
  proof(cases)
    case 1 then show ?thesis by blast  
  next
    case 2 then show ?thesis by simp
  next
    case 3
    then have "delta x1 y1 x2 y2 = 0" "delta' x1 y1 x2 y2 = 0"
      unfolding p_def q_def e_aff_0_def e_aff_1_def using assms 
      by (simp add: assms p_def q_def)+
    have "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
      using \<open>delta x1 y1 x2 y2 = 0\<close> 
      unfolding delta_def delta_plus_def delta_minus_def by auto
    then have "p \<in> e_circ" "q \<in> e_circ"
      unfolding e_circ_def using assms p_def q_def by auto
    
    obtain a0 b0 where tq_expr: "\<tau> q = (a0,b0)" by fastforce
    obtain a1 b1 where p_expr: "p = (a1,b1)" by fastforce
    from tq_expr have q_expr: "q = \<tau> (a0,b0)" using tau_idemp_explicit q_def by auto
 
    have a0_nz: "a0 \<noteq> 0" "b0 \<noteq> 0"
      using \<open>\<tau> q = (a0, b0)\<close> \<open>x2 \<noteq> 0\<close> \<open>y2 \<noteq> 0\<close> comp_apply q_def tau_sq by auto

    have a1_nz: "a1 \<noteq> 0" "b1 \<noteq> 0"
      using \<open>p = (a1, b1)\<close> \<open>x1 \<noteq> 0\<close> \<open>y1 \<noteq> 0\<close> p_def by auto

    have in_aff: "(a0,b0) \<in> e_aff" "(a1,b1) \<in> e_aff"
      using \<open>q \<in> e_circ\<close> \<tau>_circ circ_to_aff tq_expr apply fastforce
      using assms(1) p_expr by auto

    define \<delta>' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where 
      "\<delta>'= (\<lambda> x0 y0. x0 * y0 * delta_minus a1 b1 (1/(t*x0)) (1/(t*y0)))" 
    define p\<delta>' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where 
      "p\<delta>'= (\<lambda> x0 y0. x0 * y0 * delta_plus a1 b1 (1/(t*x0)) (1/(t*y0)))" 
    define \<delta>_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
      "\<delta>_plus = (\<lambda> x0 y0. t * x0 * y0 * delta_x a1 b1 (1/(t*x0)) (1/(t*y0)))"
    define \<delta>_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
      "\<delta>_minus = (\<lambda> x0 y0. t * x0 * y0 * delta_y a1 b1 (1/(t*x0)) (1/(t*y0)))"

    have \<delta>'_expr: "\<delta>' a0 b0 = a0*b0 - a1*b1"
     unfolding \<delta>'_def delta_minus_def 
     by(simp add: algebra_simps a0_nz a1_nz power2_eq_square[symmetric] t_expr d_nz)
    have p\<delta>'_expr: "p\<delta>' a0 b0 = a0 * b0 + a1 * b1"
      unfolding p\<delta>'_def delta_plus_def 
      by(simp add: algebra_simps a0_nz a1_nz power2_eq_square[symmetric] t_expr d_nz)
    have \<delta>_plus_expr: "\<delta>_plus a0 b0 = b1 * b0 - a1 * a0" 
      unfolding \<delta>_plus_def delta_x_def
      by(simp add: divide_simps a0_nz a1_nz t_nz)
    have \<delta>_minus_expr: "\<delta>_minus a0 b0 = a1 * b0 + b1 * a0" 
      unfolding \<delta>_minus_def delta_y_def
      by(simp add: divide_simps a0_nz a1_nz t_nz)              

    (* cases to consider *)
    have cases1: "\<delta>' a0 b0 = 0 \<or> p\<delta>' a0 b0 = 0"
      unfolding \<delta>'_def p\<delta>'_def  
      using \<open>delta x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> delta_def p_def q_def q_expr by auto
    have cases2: "\<delta>_minus a0 b0 = 0 \<or> \<delta>_plus a0 b0 = 0" 
      using \<delta>_minus_def \<delta>_plus_def \<open>delta' x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> 
                delta'_def q_def p_def tq_expr by auto
    (* Observation: the zeroness of \<delta>' and p\<delta>' are exclusive
    have exclusive_cases:
      "\<not> (\<delta>' a0 b0 = 0 \<and> p\<delta>' a0 b0 = 0)"
      using \<delta>'_expr \<open>x1 \<noteq> 0\<close> \<open>y1 \<noteq> 0\<close> ext_add_inverse p\<delta>'_expr p_def p_expr 
      by fastforce*)
      
    consider 
      (1) "\<delta>' a0 b0 = 0" "\<delta>_minus a0 b0 = 0" |
      (2) "\<delta>' a0 b0 = 0" "\<delta>_plus a0 b0 = 0" |
      (3) "p\<delta>' a0 b0 = 0" "\<delta>_minus a0 b0 = 0" |
      (4) "p\<delta>' a0 b0 = 0" "\<delta>_minus a0 b0 \<noteq> 0" 
       using cases1 cases2 by auto
    then have "(a0,b0) = (b1,a1) \<or> (a0,b0) = (-b1,-a1) \<or> 
                (a0,b0) = (a1,-b1) \<or> (a0,b0) = (-a1,b1)" 
    proof(cases)
      case 1
      have zeros: "a0 * b0 - a1 * b1 = 0" "a1 * b0 + a0 * b1 = 0"
        using 1 \<delta>_minus_expr \<delta>'_expr 
        by(simp_all add: algebra_simps) 
      have "\<exists> q1 q2 q3 q4.
        2*a0*b0*(b0^2 - a1^2) = 
            q1*(-1 + a0^2 + b0^2 - t^2 * a0^2 * b0^2) +
            q2*(-1 + a1^2 + b1^2 - t^2 * a1^2 * b1^2) +
            q3*(a0 * b0 - a1 * b1) +
            q4*(a1 * b0 + a0 * b1)"   
        by algebra     
      then have "b0\<^sup>2 - a1\<^sup>2 = 0" "a0\<^sup>2 - b1\<^sup>2 = 0" "a0 * b0 - a1 * b1 = 0" 
        using a0_nz in_aff zeros 
        unfolding e_aff_def e_def 
          apply simp_all 
         apply(simp_all add: algebra_simps two_not_zero)
        by algebra 
      then show ?thesis 
        by algebra
    next
      case 2
      have zeros: "b1 * b0 - a1 * a0 = 0" "a0 * b0 - a1 * b1 = 0" 
        using 2 \<delta>_plus_expr \<delta>'_expr by auto 
      have "b0\<^sup>2 - a1\<^sup>2 = 0" "a0\<^sup>2 - b1\<^sup>2 = 0" "a0 * b0 - a1 * b1 = 0" 
        using in_aff zeros
        unfolding e_aff_def e_def
        apply simp_all 
        by algebra+ 
      then show ?thesis 
        by algebra
    next
      case 3
      have zeros: "a1 * b0 + b1 * a0 = 0" "a0 * b0 + a1 * b1 = 0" 
        using 3 \<delta>_minus_expr p\<delta>'_expr by auto
      have "a0\<^sup>2 - a1\<^sup>2 = 0" "b0\<^sup>2 - b1\<^sup>2 = 0" "a0 * b0 + a1 * b1 = 0" 
        using in_aff zeros
        unfolding e_aff_def e_def
        apply simp_all 
        by algebra+ 
      then show ?thesis 
        by algebra
    next
      case 4
      have zeros: "a0 * b0 + a1 * b1 = 0" "a1 * b0 + b1 * a0 \<noteq> 0" 
        using 4 p\<delta>'_expr \<delta>_minus_expr \<delta>'_expr by auto
      have "a0^2-b1^2 = 0" "a1^2 - b0^2  = 0"
        using in_aff zeros
        unfolding e_aff_def e_def 
        by(simp_all,algebra+)
      then show ?thesis 
        using cases2 \<delta>_minus_expr \<delta>_plus_expr by algebra
    qed

    then have "(a0,b0) \<in> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
      unfolding p_expr by auto      
    then have "\<exists> g \<in> rotations. \<tau> q = (g \<circ> i) p"
      unfolding rotations_def by (auto simp add: \<open>\<tau> q = (a0, b0)\<close>)
    then obtain g where "g \<in> rotations" "\<tau> q = (g \<circ> i) p" by blast
    then have "q = (\<tau> \<circ> g \<circ> i) p"
      using tau_sq \<open>\<tau> q = (a0, b0)\<close> q_def by auto
    then have "\<exists>g\<in>symmetries. q = (g \<circ> i) p"
      using tau_rot_sym \<open>g \<in> rotations\<close> symmetries_def by blast     
    then show ?thesis 
      using \<open>p \<in> e_circ\<close> by blast
  qed
qed

lemma dichotomy_2:
  assumes "add (x1,y1) (x2,y2) = (1,0)" 
          "((x1,y1),(x2,y2)) \<in> e_aff_0"
  shows "(x2,y2) = i (x1,y1)"
proof -
  have 1: "x1 = x2"
    using assms(1,2) unfolding e_aff_0_def e_aff_def delta_def delta_plus_def 
                               delta_minus_def e_def
    apply(simp) 
    apply(simp add: t_expr) 
    by algebra

  have 2: "y1 = - y2"
    using assms(1,2) unfolding e_aff_0_def e_aff_def delta_def delta_plus_def 
                               delta_minus_def e_def
    apply(simp) 
    apply(simp add: t_expr)
    by algebra

  from 1 2 show ?thesis by simp
qed
  
(*TODO: once the field is generalized, algebra stops automatically solving this goal*)       
lemma dichotomy_3:
  assumes "ext_add (x1,y1) (x2,y2) = (1,0)" 
          "((x1,y1),(x2,y2)) \<in> e_aff_1"
  shows "(x2,y2) = i (x1,y1)"
proof -
  have nz: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
    using assms by(simp,force)+
  have in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
    using assms unfolding e_aff_1_def by auto
  have ds: "delta' x1 y1 x2 y2 \<noteq> 0"
    using assms unfolding e_aff_1_def by auto

  have eqs: "x1*(y1+y2) = x2*(y1+y2)" "x1 * y1 + x2 * y2 = 0" 
    using assms in_aff ds
    unfolding e_aff_def e_def delta'_def delta_x_def delta_y_def
    apply simp_all
    by algebra
    
  then consider (1) "y1 + y2 = 0" | (2) "x1 = x2" by auto
  then have 1: "x1 = x2"
  proof(cases)
    case 1
    then show ?thesis 
      using eqs nz by algebra
  next
    case 2
    then show ?thesis by auto
  qed

  have 2: "y1 = - y2"
    using eqs 1 nz
    by algebra

  from 1 2 show ?thesis by simp
qed

subsubsection \<open>Meaning of dichotomy condition on deltas\<close>

lemma wd_d_nz:
  assumes "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" "(x,y) \<in> e_circ"
  shows "delta x y x' y' = 0"
  using assms unfolding symmetries_def e_circ_def delta_def delta_minus_def delta_plus_def
  by(auto,auto simp add: divide_simps t_nz t_expr(1) power2_eq_square[symmetric] d_nz)

lemma wd_d'_nz:
  assumes "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" "(x,y) \<in> e_circ"
  shows "delta' x y x' y' = 0"
  using assms unfolding symmetries_def e_circ_def delta'_def delta_x_def delta_y_def
  by auto

lemma meaning_of_dichotomy_1:
  assumes "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))"  
  shows "fst (add (x1,y1) (x2,y2)) = 0 \<or> snd (add (x1,y1) (x2,y2)) = 0" 
  using assms
  apply(simp)
  unfolding symmetries_def
  apply(safe)
  apply(simp_all) 
  apply(simp_all split: if_splits add: t_nz divide_simps) 
  by(simp_all add: algebra_simps t_nz divide_simps power2_eq_square[symmetric] t_expr)


(* TODO: there is a problem in showing the converse of these lemmas.
    the idea is to use dichotomy_2 but for that we need some delta tau to be non-zero
    which in applications seems not easy to deduce *)
lemma meaning_of_dichotomy_2:
  assumes "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))"  
  shows "fst (ext_add (x1,y1) (x2,y2)) = 0 \<or> snd (ext_add (x1,y1) (x2,y2)) = 0" 
  using assms
  apply(simp)
  unfolding symmetries_def
  apply(safe)
  apply(simp_all) 
  by(simp_all split: if_splits add: t_nz divide_simps) 

subsection \<open>Gluing relation and projective points\<close>

definition gluing :: "((('a \<times> 'a) \<times> bit) \<times> (('a \<times> 'a) \<times> bit)) set" where
  "gluing = {(((x0,y0),l),((x1,y1),j)). 
               ((x0,y0) \<in> e_aff \<and> (x1,y1) \<in> e_aff) \<and>
               ((x0 \<noteq> 0 \<and> y0 \<noteq> 0 \<and> (x1,y1) = \<tau> (x0,y0) \<and> j = l+1) \<or>
                (x0 = x1 \<and> y0 = y1 \<and> l = j))}"

abbreviation gluing_class ("\<langle>_\<rangle>" 1000) where "\<langle>p\<rangle> \<equiv> gluing `` {p}"

lemma gluing_char:
  assumes "((p0,l),(p1,j)) \<in> gluing"
  shows "(p0 = p1 \<and> l = j) \<or> (p1 = \<tau> p0 \<and> j = l+1 \<and> fst p0 \<noteq> 0 \<and> snd p0 \<noteq> 0)"
proof -
  obtain x0 y0 x1 y1 where p_eqs: "p0 = (x0,y0)" "p1 = (x1,y1)" by fastforce+
  show ?thesis
    using assms 
    unfolding p_eqs gluing_def
    by auto
qed

lemma gluing_char_zero:
  assumes "(((x0,y0),l),((x1,y1),j)) \<in> gluing" "x0 = 0 \<or> y0 = 0"
  shows "(x0,y0) = (x1,y1) \<and> l = j"
  using assms unfolding gluing_def e_circ_def by force

lemma gluing_aff:
  assumes "((p0,l),(p1,j)) \<in> gluing"
  shows "p0 \<in> e_aff" "p1 \<in> e_aff"
proof -
  obtain x0 y0 x1 y1 where "p0 = (x0,y0)" "p1 = (x1,y1)"
    by fastforce+
  then show "p0 \<in> e_aff" "p1 \<in> e_aff"
    using assms unfolding gluing_def by force+
qed

definition e_aff_bit :: "(('a \<times> 'a) \<times> bit) set" where
 "e_aff_bit = e_aff \<times> UNIV"

lemma eq_rel: "equiv e_aff_bit gluing"
  unfolding equiv_def
proof(safe)
  show "refl_on e_aff_bit gluing"
    unfolding refl_on_def e_aff_bit_def gluing_def by auto
  show "sym gluing" 
    unfolding sym_def gluing_def by(auto simp add: e_circ_def t_nz)
  show "trans gluing"
    unfolding trans_def gluing_def by(auto simp add: e_circ_def t_nz)
qed

definition e_proj where "e_proj = e_aff_bit // gluing"

subsubsection\<open>Point-class classification\<close>

lemma eq_class_simp:
  assumes "X \<in> e_proj" "X \<noteq> {}"
  shows "X // gluing = {X}"  
  
proof - 
  have simp_un: "gluing `` {x} = X" if "x \<in> X"  for x
    apply(rule quotientE)
      using e_proj_def assms(1) apply blast
      using equiv_class_eq[OF eq_rel] that by auto

  show "X // gluing = {X}"
    unfolding quotient_def by(simp add: simp_un assms)
qed

lemma gluing_class_1:
  assumes "fst p = 0 \<or> snd p = 0" "p \<in> e_aff"
  shows "gluing `` {(p, l)} = {(p, l)}"
proof - 
  have "p \<notin> e_circ" 
    using assms unfolding e_circ_def
    by(cases "p",auto)
  then show ?thesis
    using assms unfolding gluing_def Image_def
    by(cases "p",simp split: prod.splits del: \<tau>.simps add: assms,safe)
qed

lemma gluing_class_2:
  assumes "fst p \<noteq> 0" "snd p \<noteq> 0" "p \<in> e_aff"
  shows "gluing `` {(p, l)} = {(p, l), (\<tau> p, l + 1)}"
proof - 
  have "p \<in> e_circ" using assms unfolding e_circ_def by(cases "p",force) 
  then have "\<tau> p \<in> e_aff"
    using \<tau>_circ using e_circ_def by(cases "p",force) 
   show ?thesis
    using assms unfolding gluing_def Image_def
    apply(cases "p",simp add: e_circ_def assms del: \<tau>.simps,safe) 
    using \<open>\<tau> p \<in> e_aff\<close> by argo 
qed

lemma e_proj_elim_1:
  assumes "p \<in> e_aff"
  shows "{(p,l)} \<in> e_proj \<longleftrightarrow> fst p = 0 \<or> snd p = 0"
proof
  assume as: "{(p, l)} \<in> e_proj" 
  have eq: "\<langle>(p,l)\<rangle> = {(p,l)}"
    (is "_ = ?B")
   using quotientI[of _ ?B gluing] eq_class_simp as by auto
  then show "fst p = 0 \<or> snd p = 0" 
    using assms gluing_class_2 by force
next
  assume "fst p = 0 \<or> snd p = 0"
  then have eq: "\<langle>(p,l)\<rangle> = {(p,l)}"
    using assms gluing_class_1 by presburger
  show "{(p,l)} \<in> e_proj"
    apply(subst eq[symmetric])  
    unfolding e_proj_def apply(rule quotientI)
    unfolding e_aff_bit_def using assms by simp  
qed

lemma e_proj_elim_2:
  assumes "p \<in> e_aff"
  shows "{(p,l),(\<tau> p,l+1)} \<in> e_proj \<longleftrightarrow> fst p \<noteq> 0 \<and> snd p \<noteq> 0"
proof 
  assume "fst p \<noteq> 0 \<and> snd p \<noteq> 0"
  then have eq: "\<langle>(p,l)\<rangle> = {(p,l),(\<tau> p,l+1)}"
    using assms gluing_class_2 by presburger
  show "{(p,l),(\<tau> p,l+1)} \<in> e_proj"
    apply(subst eq[symmetric])  
    unfolding e_proj_def apply(rule quotientI)
    unfolding e_aff_bit_def using assms by simp  
next
  assume as: "{(p, l), (\<tau> p, l + 1)} \<in> e_proj" 
  have eq: "\<langle>(p,l)\<rangle> = {(p,l),(\<tau> p,l+1)}"
    (is "_ = ?B")
   using quotientI[of _ ?B gluing] eq_class_simp as by auto
  then show "fst p \<noteq> 0 \<and> snd p \<noteq> 0" 
    using assms gluing_class_1 by fastforce
qed

lemma e_proj_eq:
  assumes "p \<in> e_proj"
  shows "\<exists> x y l. (p = {((x,y),l)} \<or> p = {((x,y),l),(\<tau> (x,y),l+1)}) \<and> (x,y) \<in> e_aff"      
proof -
  obtain g where p_expr: "p = gluing `` {g}" "g \<in> e_aff_bit"
    using assms unfolding e_proj_def quotient_def by blast+
  then obtain x y l where g_expr: "g = ((x,y),l)" "(x,y) \<in> e_aff" 
    using e_aff_bit_def by auto
  show ?thesis
    using e_proj_elim_1 e_proj_elim_2 gluing_class_1 gluing_class_2 g_expr p_expr by meson
qed

lemma e_proj_aff:
  "\<langle>(p,l)\<rangle> \<in> e_proj \<longleftrightarrow> p \<in> e_aff"
proof 
  assume "\<langle>(p,l)\<rangle> \<in> e_proj"
  then show "p \<in> e_aff"
    apply(cases "p")
    unfolding e_proj_def e_aff_bit_def 
    apply(rule quotientE)
    using eq_equiv_class gluing_aff 
          e_aff_bit_def eq_rel by fastforce+
next
  assume as: "p \<in> e_aff"
  show "\<langle>(p,l)\<rangle> \<in> e_proj"
    apply(cases "p")
    using gluing_class_1[OF _ as] gluing_class_2[OF _ _ as]
          e_proj_elim_1[OF as]
    using gluing_class_1[OF _ as] gluing_class_2[OF _ _ as]
          e_proj_elim_1[OF as] e_proj_elim_2[OF as] by fastforce    
qed

lemma gluing_cases:
  assumes "x \<in> e_proj"
  obtains x0 y0 l where "x = {((x0,y0),l)} \<or> x = {((x0,y0),l),(\<tau> (x0,y0),l+1)}"
  using e_proj_eq[OF assms] that by blast

lemma gluing_cases_explicit:
  assumes "x \<in> e_proj" "x = gluing `` {((x0,y0),l)}"
  shows "x = {((x0,y0),l)} \<or> x = {((x0,y0),l),(\<tau> (x0,y0),l+1)}"  
proof -
  have "(x0,y0) \<in> e_aff"
    using assms e_proj_aff by simp
  have "gluing `` {((x0,y0),l)} = {((x0,y0),l)} \<or> 
        gluing `` {((x0,y0),l)} = {((x0,y0),l),(\<tau> (x0,y0),l+1)}"
    using assms gluing_class_1 gluing_class_2 \<open>(x0, y0) \<in> e_aff\<close> by meson   
  then show ?thesis using assms by fast
qed

lemma gluing_cases_points:
  assumes "x \<in> e_proj" "x = gluing `` {(p,l)}"
  shows "x = {(p,l)} \<or> x = {(p,l),(\<tau> p,l+1)}"  
  using gluing_cases_explicit[OF assms(1), of "fst p" "snd p" l] assms by auto

lemma identity_equiv: 
  "\<langle>((1,0),l)\<rangle> = {((1,0),l)}"
  unfolding Image_def
proof(simp,standard)
  show "{y. (((1, 0), l), y) \<in> gluing} \<subseteq> {((1, 0), l)}"    
    using gluing_char_zero by(intro subrelI,fast) 
  have "(1,0) \<in> e_aff" 
    unfolding e_aff_def e_def by simp
  then have "((1, 0), l) \<in> e_aff_bit"
    using zero_bit_def unfolding e_aff_bit_def  by blast
  show "{((1, 0), l)} \<subseteq> {y. (((1, 0), l), y) \<in> gluing}"
    using eq_rel \<open>((1, 0), l) \<in> e_aff_bit\<close> 
    unfolding equiv_def refl_on_def by blast
qed

lemma identity_proj:
  "{((1,0),l)} \<in> e_proj"
proof -
  have "(1,0) \<in> e_aff"
    unfolding e_aff_def e_def by auto
  then show ?thesis
    using e_proj_aff[of "(1,0)" l] identity_equiv by auto
qed
  
lemma gluing_inv:
  assumes "x \<noteq> 0" "y \<noteq> 0" "(x,y) \<in> e_aff"
  shows "gluing `` {((x,y),j)} = gluing `` {(\<tau> (x,y),j+1)}"
proof -
  have taus: "\<tau> (x,y) \<in> e_aff" 
    using e_circ_def assms \<tau>_circ by fastforce+ 

  have "gluing `` {((x,y), j)} =  {((x, y), j), (\<tau> (x, y), j + 1)}"
    using gluing_class_2 assms by simp
  also have "... = {(\<tau> (x, y), j+1), (\<tau> (\<tau> (x, y)), j)}"
    using tau_idemp_explicit by force
  also have "{(\<tau> (x, y), j+1), (\<tau> (\<tau> (x, y)), j)} = gluing `` {(\<tau> (x,y), j + 1)}"
    apply(subst gluing_class_2[of "(\<tau> (x,y))"])
    using assms taus t_nz by auto
  finally show ?thesis by blast
qed 


subsection \<open>Projective addition on points\<close>

subsubsection \<open>Properties of proj_add\<close>

function (domintros) proj_add :: "('a \<times> 'a) \<times> bit \<Rightarrow> ('a \<times> 'a) \<times> bit \<Rightarrow> ('a \<times> 'a) \<times> bit"
  where 
    "proj_add ((x1, y1), l) ((x2, y2), j) = (add (x1, y1) (x2, y2), l+j)"
   if "delta x1 y1 x2 y2 \<noteq> 0" and 
     "(x1, y1) \<in> e_aff" and 
     "(x2, y2) \<in> e_aff" 
  | "proj_add ((x1, y1), l) ((x2, y2), j) = (ext_add (x1, y1) (x2, y2), l+j)"
   if "delta' x1 y1 x2 y2 \<noteq> 0" and 
     "(x1, y1) \<in> e_aff" and 
     "(x2, y2) \<in> e_aff"
  | "proj_add ((x1, y1), l) ((x2, y2), j) = undefined" 
   if "(x1, y1) \<notin> e_aff \<or> (x2, y2) \<notin> e_aff \<or> 
        (delta x1 y1 x2 y2 = 0 \<and> delta' x1 y1 x2 y2 = 0)"
  apply(fast)
  apply(fastforce)
  using coherence e_aff_def apply force
  by auto

termination proj_add using "termination" by blast

lemma proj_add_inv:
  assumes "(x0,y0) \<in> e_aff"
  shows "proj_add ((x0,y0),l) (i (x0,y0),l') = ((1,0),l+l')"
proof -
  have i_in: "i (x0,y0) \<in> e_aff"
    using i_aff assms by blast

  consider (1) "x0 = 0" | (2) "y0 = 0" | (3) "x0 \<noteq> 0" "y0 \<noteq> 0" by fast
  then show ?thesis
  proof(cases)
    case 1
    from assms 1 have y_expr: "y0 = 1 \<or> y0 = -1" 
      unfolding e_aff_def e_def by(simp,algebra) 
    then have "delta x0 y0 x0 (-y0) \<noteq> 0"
      using 1 unfolding delta_def delta_minus_def delta_plus_def by simp
    then show "proj_add ((x0,y0),l) (i (x0,y0),l') = ((1,0),l+l')"  
      using 1  assms delta_plus_def i_in inverse_generalized by fastforce     
  next
    case 2
    from assms 2 have "x0 = 1 \<or> x0 = -1" 
      unfolding e_aff_def e_def by(simp,algebra) 
    then have "delta x0 y0 x0 (-y0) \<noteq> 0"
      using 2 unfolding delta_def delta_minus_def delta_plus_def by simp
    then show ?thesis  
      using 2 assms delta_def inverse_generalized by fastforce
  next
    case 3

    consider (a) "delta x0 y0 x0 (-y0) = 0" "delta' x0 y0 x0 (-y0) = 0" |
             (b) "delta x0 y0 x0 (-y0) \<noteq> 0" "delta' x0 y0 x0 (-y0) = 0" |
             (c) "delta x0 y0 x0 (-y0) = 0" "delta' x0 y0 x0 (-y0) \<noteq> 0" |
             (d) "delta x0 y0 x0 (-y0) \<noteq> 0" "delta' x0 y0 x0 (-y0) \<noteq> 0" by meson
    then show ?thesis
    proof(cases)
      case a
      then have "d * x0^2 * y0^2 = 1 \<or> d * x0^2 * y0^2 = -1" 
                "x0^2 = y0^2"
                "x0^2 + y0^2 - 1 = d * x0^2 * y0^2"
        unfolding power2_eq_square
        using a unfolding delta_def delta_plus_def delta_minus_def apply algebra
        using 3 two_not_zero a unfolding delta'_def delta_x_def delta_y_def apply force
        using assms t_expr unfolding e_aff_def e_def power2_eq_square by force
      then have "2*x0^2 = 2 \<or> 2*x0^2 = 0"
        by algebra
      then have "x0 = 1 \<or> x0 = -1"
        using 3 
        apply(simp add: two_not_zero) 
        by algebra
      then have "y0 = 0"
        using assms t_n1 t_nm1
        unfolding e_aff_def e_def 
        apply simp 
        by algebra
      then have "False"
        using 3 by auto
      then show ?thesis by auto
    next
      case b
      have "proj_add ((x0, y0), l) (i (x0, y0), l') = 
            (add (x0, y0) (i (x0, y0)), l+l')"
        using assms i_in b by simp
      also have "... = ((1,0),l+l')"
        using inverse_generalized[OF assms] b 
        unfolding delta_def delta_plus_def delta_minus_def
        by auto
      finally show ?thesis 
        by blast
    next
      case c
      have "proj_add ((x0, y0), l) (i (x0, y0), l') = 
            (ext_add (x0, y0) (i (x0, y0)), l+l')"
        using assms i_in c by simp
      also have "... = ((1,0),l+l')"
        apply(subst ext_add_inverse)
        using 3 by auto
      finally show ?thesis 
        by blast
    next
      case d
      have "proj_add ((x0, y0), l) (i (x0, y0), l') = 
            (add (x0, y0) (i (x0, y0)), l+l')"
        using assms i_in d by simp
      also have "... = ((1,0),l+l')"
        using inverse_generalized[OF assms] d
        unfolding delta_def delta_plus_def delta_minus_def
        by auto
      finally show ?thesis 
        by blast
    qed
  qed
qed

lemma proj_add_comm:
  "proj_add (p0,l) (p1,j) = proj_add (p1,j) (p0,l)"
  (is "?lhs = ?rhs") 
proof -
  obtain x0 y0 x1 y1 where p_expr: "p0 = (x0,y0)" "p1 = (x1,y1)" by fastforce
  consider 
   (1) "delta x0 y0 x1 y1 \<noteq> 0 \<and> (x0,y0)  \<in> e_aff \<and> (x1,y1) \<in> e_aff" |
   (2) "delta' x0 y0 x1 y1 \<noteq> 0 \<and> (x0,y0)  \<in> e_aff \<and> (x1,y1) \<in> e_aff" |
   (3) "(delta x0 y0 x1 y1 = 0 \<and> delta' x0 y0 x1 y1 = 0) \<or> 
         (x0,y0) \<notin> e_aff \<or> (x1,y1) \<notin> e_aff" by blast
  then show ?thesis
  proof(cases)
    case 1 then show ?thesis by (simp add: p_expr add_comm delta_com)
  next
    case 2 then show ?thesis by(simp add: p_expr ext_add_comm delta'_com del: ext_add.simps)  
  next
    case 3 then show ?thesis by(auto simp add: p_expr delta_com delta'_com)
  qed    
qed

subsubsection \<open>Properties of proj_add'\<close>

fun proj_add' :: "('a \<times> 'a) \<times> bit \<Rightarrow> ('a \<times> 'a) \<times> bit \<Rightarrow> ('a \<times> 'a) \<times> bit" where
  "proj_add' ((x1,y1),l) ((x2,y2),j) = 
    (if (delta x1 y1 x2 y2 \<noteq> 0 \<or> delta' x1 y1 x2 y2 \<noteq> 0)
     then proj_add ((x1, y1), l) ((x2, y2), j)
     else  proj_add ((x1, y1), l) (\<tau> (x2, y2), j+1))"

subsection \<open>Projective addition on classes\<close>

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
              ((x1, y1), (x2, y2)) \<in> e_aff_0 \<union> e_aff_1
          } // gluing
        )" 
   if "c1 \<in> e_proj" and "c2 \<in> e_proj" 
  | "proj_add_class c1 c2 = undefined" 
   if "c1 \<notin> e_proj \<or> c2 \<notin> e_proj" 
  by (meson surj_pair) auto

termination proj_add_class using "termination" by auto

definition proj_addition (infix "\<oplus>" 600) where 
  "proj_addition c1 c2 = the_elem (proj_add_class c1 c2)"

subsubsection \<open>Covering\<close>

(* We formulate covering on classes so there is no need to prove that 
  there exists exactly one point. *)

corollary no_fp_eq:
  assumes "p \<in> e_circ" 
  assumes "r' \<in> rotations" "r \<in> rotations"
  assumes "(r' \<circ> i) p = (\<tau> \<circ> r) (i p)"
  shows "False" 
proof -
  obtain r'' where "r'' \<circ> r' = id" "r'' \<in> rotations" 
    using rot_inv assms by blast
  then have "i p = (r'' \<circ> \<tau> \<circ> r) (i p)"
    using assms by (simp,metis pointfree_idE)
  then have "i p = (\<tau> \<circ> r'' \<circ> r) (i p)"
    using rot_tau_com[OF \<open>r'' \<in> rotations\<close>] by simp
  then have "\<exists> r''. r'' \<in> rotations \<and> i p = (\<tau> \<circ> r'') (i p)"
    using rot_comp[OF \<open>r'' \<in> rotations\<close>] assms by fastforce 
  then obtain r'' where 
    eq: "r'' \<in> rotations" "i p = (\<tau> \<circ> r'') (i p)"
    by blast
  have "\<tau> \<circ> r'' \<in> G" "i p \<in> e_circ" 
    using tau_rot_sym[OF \<open>r'' \<in> rotations\<close>] G_partition apply simp
    using i_circ_points assms(1) by simp
  then show "False" 
    using g_no_fp[OF \<open>\<tau> \<circ> r'' \<in> G\<close> \<open>i p \<in> e_circ\<close>] 
          eq assms(1) sym_not_id[OF eq(1)] by argo
qed

lemma covering:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "proj_add_class p q \<noteq> {}"
proof -
  from e_proj_eq[OF assms(1)] e_proj_eq[OF assms(2)]
  obtain x y l x' y' l' where 
    p_q_expr: "p = {((x, y), l)} \<or> p = {((x, y), l), (\<tau> (x, y), l + 1)} " 
              "q = {((x', y'), l')} \<or> q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
              "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    by blast
  then have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"  by auto
  from p_q_expr have gluings: "p = (\<langle>((x,y),l)\<rangle>)" 
                              "q = (\<langle>((x',y'),l')\<rangle>)"    
    using assms e_proj_elim_1 e_proj_elim_2 gluing_class_1 gluing_class_2
    by metis+
  then have gluing_proj: "(\<langle>((x,y),l)\<rangle>) \<in> e_proj"
                         "(\<langle>((x',y'),l')\<rangle>) \<in> e_proj" 
    using assms by blast+

  consider 
     "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | "((x, y), x', y') \<in> e_aff_0" 
   | "((x, y), x', y') \<in> e_aff_1"
    using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by blast
  then show ?thesis 
  proof(cases)
    case 1
    then obtain r where r_expr: "(x',y') = (\<tau> \<circ> r) (i (x,y))" "r \<in> rotations"
      using sym_decomp by force

    then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
      using 1 t_nz unfolding e_circ_def rotations_def by force+

    have taus: "\<tau> (x',y') \<in> e_aff" 
      using nz i_aff p_q_expr(3) r_expr rot_aff tau_idemp_point by auto

    have circ: "(x,y) \<in> e_circ" 
      using nz in_aff e_circ_def by simp

    have p_q_expr': "p = {((x,y),l),(\<tau> (x,y),l+1)}"
                    "q = {(\<tau> (x',y'),l'+1),((x',y'),l')}"
      using gluings nz gluing_class_2 taus in_aff tau_idemp_point t_nz assms by auto

    have p_q_proj: "{((x,y),l),(\<tau> (x,y),l+1)} \<in> e_proj" 
                   "{(\<tau> (x',y'),l'+1),((x',y'),l')} \<in> e_proj" 
      using p_q_expr' assms by auto

    consider
     (a)  "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (x', y') = (g \<circ> i) (x, y))" 
    |(b)  "((x, y), \<tau> (x', y')) \<in> e_aff_0" 
    |(c)  "((x, y), \<tau> (x', y')) \<in> e_aff_1"
      using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>\<tau> (x', y') \<in> e_aff\<close>] by blast  
    then show ?thesis
    proof(cases)
      case a
      then obtain r' where r'_expr: "\<tau> (x',y') = (\<tau> \<circ> r') (i (x, y))" "r' \<in> rotations"
        using sym_decomp by force
      have "(x',y') = r' (i (x, y))"
      proof- 
        have "(x',y') = \<tau> (\<tau> (x',y'))"
          using tau_idemp_point by presburger
        also have "... = \<tau> ((\<tau> \<circ> r') (i (x, y)))"
          using r'_expr by argo
        also have "... = r' (i (x, y))"
          using tau_idemp_point by simp
        finally show ?thesis by simp
      qed
      then have "False"
        using no_fp_eq[OF circ r'_expr(2) r_expr(2)] r_expr by simp
      then show ?thesis by blast
    next
      case b
      then have ds: "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
        unfolding e_aff_0_def by simp 
      then have 
        add_some: "proj_add ((x,y),l) (\<tau> (x',y'),l'+1) = (add (x, y) (\<tau> (x',y')), l+l'+1)"
        using proj_add.simps[of x y _ _ l "l'+1", OF _ ] 
              \<open>(x,y) \<in> e_aff\<close> \<open>\<tau> (x', y') \<in> e_aff\<close> by force 
      then show ?thesis
        unfolding p_q_expr' proj_add_class.simps(1)[OF p_q_proj] 
        unfolding e_aff_0_def using ds in_aff taus by force
    next
      case c
      then have ds: "delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
        unfolding e_aff_1_def by simp 
      then have 
        add_some: "proj_add ((x,y),l) (\<tau> (x',y'),l'+1) = (ext_add (x, y) (\<tau> (x',y')), l+l'+1)"
        using proj_add.simps[of x y _ _ l "l'+1", OF _ ] 
              \<open>(x,y) \<in> e_aff\<close> \<open>\<tau> (x', y') \<in> e_aff\<close> by force 
      then show ?thesis
        unfolding p_q_expr' proj_add_class.simps(1)[OF p_q_proj] 
        unfolding e_aff_1_def using ds in_aff taus by force
  qed
  next
    case 2
    then have ds: "delta x y x' y' \<noteq> 0" 
      unfolding e_aff_0_def by simp
    then have
      add_some: "proj_add ((x,y),l) ((x',y'),l') = (add (x, y) (x',y'), l+l')"
      using proj_add.simps(1)[of x y x' y' l "l'", OF _ ] in_aff by blast
    then show ?thesis 
      using p_q_expr 
      unfolding  proj_add_class.simps(1)[OF assms] 
      unfolding e_aff_0_def using ds in_aff by fast
  next
    case 3
    then have ds: "delta' x y x' y' \<noteq> 0" 
      unfolding e_aff_1_def by simp
    then have
      add_some: "proj_add ((x,y),l) ((x',y'),l') = (ext_add (x, y) (x',y'), l+l')"
      using proj_add.simps(2)[of x y x' y' l "l'", OF _ ] in_aff by blast
    then show ?thesis 
      using p_q_expr 
      unfolding  proj_add_class.simps(1)[OF assms] 
      unfolding e_aff_1_def using ds in_aff by fast
  qed
qed

lemma covering_with_deltas:
  assumes "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"
  shows "delta x y x' y' \<noteq> 0 \<or> delta' x y x' y' \<noteq> 0 \<or>
         delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0 \<or>
         delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
proof -
  fix l l'
  have proj: "(\<langle>((x,y),l)\<rangle>) \<in> e_proj" "(\<langle>((x',y'),l')\<rangle>) \<in> e_proj" 
    by (auto simp add: assms e_proj_aff)
  define p where "p = (\<langle>((x,y),l)\<rangle>)"
  define q where "q = (\<langle>((x',y'),l')\<rangle>)"
  have "p \<in> e_aff_bit // gluing"
    using proj p_def unfolding e_proj_def by blast
  from e_proj_eq[OF proj(1)] e_proj_eq[OF proj(2)]
  have
    p_q_expr: "p = {((x, y), l)} \<or> p = {((x, y), l), (\<tau> (x, y), l + 1)} " 
    "q = {((x', y'), l')} \<or> q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
    using p_def q_def 
    using proj gluing_cases_explicit apply auto[1]
    using proj gluing_cases_explicit q_def by auto
  then have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" using assms by auto

  then have gluings: "p = (\<langle>((x,y),l)\<rangle>)" 
                     "q = (\<langle>((x',y'),l')\<rangle>)"
    using p_def q_def by simp+

  then have gluing_proj: "(\<langle>((x,y),l)\<rangle>) \<in> e_proj"
                         "(\<langle>((x',y'),l')\<rangle>) \<in> e_proj" 
    using proj by blast+

  consider 
     "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | "((x, y), x', y') \<in> e_aff_0" 
   | "((x, y), x', y') \<in> e_aff_1"
    using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by blast
  then show ?thesis 
  proof(cases)
    case 1
    then obtain r where r_expr: "(x',y') = (\<tau> \<circ> r) (i (x,y))" "r \<in> rotations"
      using sym_decomp by force

    then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
      using 1 t_nz unfolding e_circ_def rotations_def by force+

    have taus: "\<tau> (x',y') \<in> e_aff" 
      using nz i_aff in_aff r_expr rot_aff tau_idemp_point by auto

    have circ: "(x,y) \<in> e_circ" 
      using nz in_aff e_circ_def by auto

    have p_q_expr': "p = {((x,y),l),(\<tau> (x,y),l+1)}"
                    "q = {(\<tau> (x',y'),l'+1),((x',y'),l')}"
      using gluings nz gluing_class_2 taus in_aff tau_idemp_point t_nz assms by auto

    have p_q_proj: "{((x,y),l),(\<tau> (x,y),l+1)} \<in> e_proj" 
                   "{(\<tau> (x',y'),l'+1),((x',y'),l')} \<in> e_proj" 
      using p_q_expr p_q_expr' assms gluing_proj gluings by auto

    consider
      (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (x', y') = (g \<circ> i) (x, y))" 
    | (b) "((x, y), \<tau> (x', y')) \<in> e_aff_0" 
    | (c) "((x, y), \<tau> (x', y')) \<in> e_aff_1"
      using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>\<tau> (x', y') \<in> e_aff\<close>] by blast  
    then show ?thesis
    proof(cases)
      case a
      then obtain r' where r'_expr: "\<tau> (x',y') = (\<tau> \<circ> r') (i (x, y))" "r' \<in> rotations"
        using sym_decomp by force
      have "(x',y') = r' (i (x, y))"
      proof- 
        have "(x',y') = \<tau> (\<tau> (x',y'))"
          using tau_idemp_point by presburger
        also have "... = \<tau> ((\<tau> \<circ> r') (i (x, y)))"
          using r'_expr by argo
        also have "... = r' (i (x, y))"
          using tau_idemp_point by simp
        finally show ?thesis by simp
      qed
      then have "False"
        using no_fp_eq[OF circ r'_expr(2) r_expr(2)] r_expr by simp
      then show ?thesis by blast
    next
      case b
      define x'' where "x'' = fst (\<tau> (x',y'))"
      define y'' where "y'' = snd (\<tau> (x',y'))"
      from b have "delta x y x'' y'' \<noteq> 0"
        unfolding e_aff_0_def using x''_def y''_def by simp 
      then show ?thesis 
        unfolding x''_def y''_def by blast
    next
      case c
      define x'' where "x'' = fst (\<tau> (x',y'))"
      define y'' where "y'' = snd (\<tau> (x',y'))"
      from c have "delta' x y x'' y'' \<noteq> 0"
        unfolding e_aff_1_def using x''_def y''_def by simp 
      then show ?thesis
        unfolding x''_def y''_def by blast
  qed
  next
    case 2
    then have "delta x y x' y' \<noteq> 0" 
      unfolding e_aff_0_def by simp
    then show ?thesis by simp
  next
    case 3
    then have "delta' x y x' y' \<noteq> 0" 
      unfolding e_aff_1_def by simp
    then show ?thesis by simp
  qed
qed


subsubsection \<open>Independence of the representant\<close>

(* TODO: this does not use independence of the representant *)
lemma proj_add_class_comm:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj" 
  shows "proj_add_class c1 c2 = proj_add_class c2 c1"
proof - 
  have "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1 \<Longrightarrow> 
        ((x2, y2), x1, y1) \<in> e_aff_0 \<union> e_aff_1" for x1 y1 x2 y2
    unfolding e_aff_0_def e_aff_1_def
              e_aff_def e_def 
              delta_def delta_plus_def delta_minus_def
              delta'_def delta_x_def delta_y_def 
    by(simp,algebra) 
  then have "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
     ((x1, y1), i) \<in> c1 \<and> ((x2, y2), j) \<in> c2 \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
        {proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
     ((x1, y1), i) \<in> c2 \<and> ((x2, y2), j) \<in> c1 \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1}"
    using proj_add_comm by blast
  then show ?thesis   
    unfolding proj_add_class.simps(1)[OF assms]
                proj_add_class.simps(1)[OF assms(2) assms(1)] by argo
qed



lemma gluing_add_1: 
  assumes "\<langle>((x,y),l)\<rangle> = {((x, y), l)}" "\<langle>((x',y'),l')\<rangle> = {((x', y'), l')}" 
          "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>((x',y'),l')\<rangle> \<in> e_proj" "delta x y x' y' \<noteq> 0"
  shows "\<langle>((x,y),l)\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = \<langle>(add (x,y) (x',y'),l+l')\<rangle>"
proof -
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have add_in: "add (x, y) (x', y') \<in> e_aff"
    using add_closure \<open>delta x y x' y' \<noteq> 0\<close> delta_def e_aff_def by auto
  from in_aff have zeros: "x = 0 \<or> y = 0" "x' = 0 \<or> y' = 0"
    using e_proj_elim_1 assms by auto
  then have add_zeros: "fst (add (x,y) (x',y')) = 0 \<or> snd (add (x,y) (x',y')) = 0"
    by auto
  then have add_proj: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> = {(add (x, y) (x', y'), l + l')}" 
    using add_in gluing_class_1 by auto
  have e_proj: "\<langle>((x,y),l)\<rangle> \<in> e_proj"
               "\<langle>((x',y'),l')\<rangle> \<in> e_proj"
               "\<langle>(add (x,y) (x',y'),l+l')\<rangle> \<in> e_proj"
    using e_proj_aff in_aff add_in by auto
    
  consider
    (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
    (b) "((x, y), x', y') \<in> e_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
    (c) "((x, y), x', y') \<in> e_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e_aff_0"
    using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by argo
  then show ?thesis
  proof(cases)
    case a
    then have "False"
      using in_aff zeros unfolding e_circ_def by force
    then show ?thesis by simp
  next
    case b
    have add_eq: "proj_add ((x, y), l) ((x', y'), l') = (add (x,y) (x', y'), l+l')"
      using proj_add.simps \<open>delta x y x' y' \<noteq> 0\<close> in_aff by simp
    show ?thesis
      unfolding proj_addition_def
      unfolding proj_add_class.simps(1)[OF e_proj(1,2)] add_proj
      unfolding assms(1,2) e_aff_0_def
      using \<open>delta x y x' y' \<noteq> 0\<close> in_aff
      apply(simp add: add_eq del: add.simps)
      apply(subst eq_class_simp)
      using add_proj e_proj by auto
  next
    case c
    then have eqs: "delta x y x' y' = 0" "delta' x y x' y' \<noteq> 0" "e x y = 0" "e x' y' = 0"
      unfolding e_aff_0_def e_aff_1_def apply fast+
      using in_aff unfolding e_aff_def by auto
    then show ?thesis using assms  by simp
  qed
qed

lemma gluing_add_2:
  assumes "\<langle>((x,y),l)\<rangle> = {((x, y), l)}" "\<langle>((x',y'),l')\<rangle> = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" 
          "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>((x',y'),l')\<rangle> \<in> e_proj" "delta x y x' y' \<noteq> 0"
  shows "\<langle>((x,y),l)\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = (\<langle>(add (x,y) (x',y'),l+l')\<rangle>)"
proof -
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have add_in: "add (x, y) (x', y') \<in> e_aff"
    using add_closure \<open>delta x y x' y' \<noteq> 0\<close> delta_def e_aff_def by auto
  from in_aff have zeros: "x = 0 \<or> y = 0" "x' \<noteq> 0"  "y' \<noteq> 0"
    using e_proj_elim_1 e_proj_elim_2 assms apply simp
    using assms(2) assms(4) e_proj_elim_2 in_aff(2) by fastforce+
  have e_proj: "\<langle>((x,y),l)\<rangle> \<in> e_proj"
               "\<langle>((x',y'),l')\<rangle> \<in> e_proj"
               "\<langle>(add (x,y) (x',y'),l+l')\<rangle> \<in> e_proj"
    using e_proj_aff in_aff add_in by auto

  consider
      (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
      (b) "((x, y), x', y') \<in> e_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
      (c) "((x, y), x', y') \<in> e_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e_aff_0"
      using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by fast
  then show ?thesis
  proof(cases)
    case a
    then have "False"
      using in_aff zeros unfolding e_circ_def by force
    then show ?thesis by simp
  next
    case b
    then have ld_nz: "delta x y x' y' \<noteq> 0" unfolding e_aff_0_def by auto    

    have v1: "proj_add ((x, y), l) ((x', y'), l') = (add (x, y) (x', y'), l + l')"
      by(simp add: \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>  ld_nz del: add.simps)

    have ecirc: "(x',y') \<in> e_circ" "x' \<noteq> 0" "y' \<noteq> 0"
      unfolding e_circ_def using zeros \<open>(x',y') \<in> e_aff\<close> by auto
    then have "\<tau> (x', y') \<in> e_circ" 
      using zeros \<tau>_circ by blast
    then have in_aff': "\<tau> (x', y') \<in> e_aff"
      unfolding e_circ_def by force

    have add_nz: "fst (add (x, y) (x', y')) \<noteq> 0" 
                 "snd (add (x, y) (x', y')) \<noteq> 0" 
      using zeros ld_nz in_aff
      unfolding delta_def delta_plus_def delta_minus_def e_aff_def e_def
      apply(simp_all)
      by auto

    have add_in: "add (x, y) (x', y') \<in> e_aff"
      using add_closure in_aff ld_nz unfolding e_aff_def delta_def by simp

    have ld_nz': "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
      unfolding delta_def delta_plus_def delta_minus_def
      using zeros by fastforce
    
    have tau_conv: "\<tau> (add (x, y) (x', y')) = add (x, y) (\<tau> (x', y'))"
      using zeros e_aff_x0[OF _ in_aff(1)] e_aff_y0[OF _ in_aff(1)] 
      apply(simp_all)
      apply(simp_all add: divide_simps d_nz t_nz)
      apply(elim disjE) 
      apply(simp_all add: t_nz zeros) 
      by auto

    have v2: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (add (x, y) (x', y')), l+l'+1)"
      using proj_add.simps \<open>\<tau> (x', y') \<in> e_aff\<close> in_aff tau_conv 
            \<open>delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0\<close> by auto    
     
    have gl_class: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> =
                {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}"
           "\<langle>(add (x,y) (x',y'),l+l')\<rangle> \<in> e_proj" 
      using gluing_class_2 add_nz add_in apply simp
      using e_proj_aff add_in by auto
   
    show ?thesis          
    proof -
      have "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and>
       ((x1, y1), x2, y2)
       \<in> {((x1, y1), x2, y2). (x1, y1) \<in> e_aff \<and> (x2, y2) \<in> e_aff \<and> delta x1 y1 x2 y2 \<noteq> 0} \<union> e_aff_1} =
      {proj_add ((x, y), l) ((x', y'), l'), proj_add ((x, y), l) (\<tau> (x', y'), l' + 1)}"
        (is "?t = _")
        using ld_nz ld_nz' in_aff in_aff' 
        apply(simp del: \<tau>.simps add.simps) 
        by force
      also have "... = {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}"
        using v1 v2 by presburger
      finally have eq: "?t = {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}"
        by blast
    
      show ?thesis
       unfolding proj_addition_def
       unfolding proj_add_class.simps(1)[OF e_proj(1,2)]
       unfolding assms(1,2) gl_class e_aff_0_def
       apply(subst eq)
       apply(subst eq_class_simp)
       using gl_class by auto
   qed
  next
   case c
    have ld_nz: "delta x y x' y' = 0" 
     using \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> c
     unfolding e_aff_0_def by force
    then have "False"
      using assms e_proj_elim_1 in_aff
      unfolding delta_def delta_minus_def delta_plus_def by blast
    then show ?thesis by blast
  qed    
qed   

lemma gluing_add_4: 
  assumes "\<langle>((x,y),l)\<rangle> = {((x, y), l), (\<tau> (x, y), l + 1)}" 
          "\<langle>((x',y'),l')\<rangle> = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
          "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>((x',y'),l')\<rangle> \<in> e_proj" "delta x y x' y' \<noteq> 0"
  shows "\<langle>((x,y),l)\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = 
         gluing `` {(add (x, y) (x',y'), l+l')}"
 (is "proj_addition ?p ?q = _")
proof -
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"
    using e_proj_aff assms by meson+
  then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
    using assms e_proj_elim_2 apply(fastforce,fastforce)
    using assms(2) assms(4) e_proj_elim_2 in_aff(2) by fastforce+
  then have circ: "(x,y) \<in> e_circ" "(x',y') \<in> e_circ"
    using in_aff e_circ_def nz by auto
  then have taus: "(\<tau> (x', y')) \<in> e_aff" "(\<tau> (x, y)) \<in> e_aff" "\<tau> (x', y') \<in> e_circ"
    using \<tau>_circ circ_to_aff by auto

  consider 
   (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (b) "((x, y), x', y') \<in> e_aff_0" 
   | (c) "((x, y), x', y') \<in> e_aff_1" "((x, y), x', y') \<notin> e_aff_0" 
    using dichotomy_1[OF in_aff] by auto
  then show ?thesis
  proof(cases)
    case a 
    then obtain g where sym_expr: "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" by auto        
    then have ds: "delta x y x' y' = 0" "delta' x y x' y' = 0"
      using wd_d_nz wd_d'_nz a by auto 
    then have "False" 
      using assms by auto
    then show ?thesis by blast    
  next
    case b
    then have ld_nz: "delta x y x' y' \<noteq> 0" 
      unfolding e_aff_0_def by auto    
    then have ds: "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" 
      unfolding delta_def delta_plus_def delta_minus_def 
      apply(simp add: algebra_simps power2_eq_square[symmetric])
      unfolding t_expr[symmetric]
      by(simp add: field_simps)
    have v1: "proj_add ((x, y), l) ((x', y'), l') = (add (x, y) (x', y'), l + l')"
      using ld_nz proj_add.simps \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> by simp
    have v2: "proj_add (\<tau> (x, y), l+1) (\<tau> (x', y'), l'+1) = (add (x, y) (x', y'), l + l')"
    proof -
      have f1: "add (x, y) (x', y') = \<tau> (ext_add (\<tau> (x, y)) (x', y'))"
        using add_ext_add_2 nz by force
      have "ext_add (\<tau> (x, y)) (x', y') = \<tau> (add (\<tau> (x, y)) (\<tau> (x', y')))"
        using inversion_invariance_2 add_ext_add nz by auto
      then show ?thesis
        using f1 ds taus by force
    qed

    consider (aaa) "delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" |
             (bbb) "delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" 
                   "delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) = 0" |
             (ccc) "delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) = 0" 
                   "delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) = 0" by blast
    then show ?thesis
    proof(cases)
      case aaa
      have tau_conv: "\<tau> (add (x, y) (\<tau> (x', y'))) = add (x,y) (x',y')"
        apply(simp)
        using aaa in_aff ld_nz 
        unfolding e_aff_def e_def delta_def delta_minus_def delta_plus_def 
        apply(safe)
        apply(simp_all add: divide_simps t_nz nz)
         apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr d_nz)
        unfolding t_expr[symmetric]
        by algebra+
      
      have v3: 
        "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (add (x, y) (x', y')), l+l'+1)" 
        using proj_add.simps \<open>(\<tau> (x', y')) \<in> e_aff\<close> 
        apply(simp del: add.simps \<tau>.simps)
        using tau_conv tau_idemp_explicit 
              proj_add.simps(1)[OF aaa \<open>(x,y) \<in> e_aff\<close>,simplified prod.collapse,OF \<open>(\<tau> (x', y')) \<in> e_aff\<close>] 
        by (metis (no_types, lifting) add.assoc prod.collapse)

      have ds': "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' \<noteq> 0"
        using aaa unfolding delta_def delta_plus_def delta_minus_def
        apply(simp add: t_nz nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)
        by(simp add: divide_simps nz t_nz)

      have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (\<tau> (add (x, y) (x', y')), l+l'+1)"
      proof -
        have "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (add (\<tau> (x, y)) (x', y'), l+l'+1)" 
          using proj_add.simps \<open>\<tau> (x,y) \<in> e_aff\<close> \<open>(x', y') \<in> e_aff\<close> ds' by auto
        moreover have "add (\<tau> (x, y)) (x', y') = \<tau> (add (x, y) (x', y'))"
          by (metis tau_idemp_point fst_conv inversion_invariance_1 nz snd_conv tau_conv)
        ultimately show ?thesis by argo          
      qed  

      have add_closure: "add (x,y) (x',y') \<in> e_aff"
        using in_aff add_closure ld_nz unfolding delta_def e_aff_def by auto

      have add_nz: "fst (add (x,y) (x',y')) \<noteq> 0"
                   "snd (add (x,y) (x',y')) \<noteq> 0"
        using ld_nz unfolding delta_def delta_minus_def   
        apply(simp_all)
        using aaa in_aff ld_nz unfolding e_aff_def e_def delta_def delta_minus_def delta_plus_def 
        apply(simp_all add: t_expr nz t_nz divide_simps)
         apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr d_nz) 
        unfolding t_expr[symmetric]
        by algebra+

      have class_eq: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> =
            {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}" 
        using  add_nz add_closure gluing_class_2 by auto
      have class_proj: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> \<in> e_proj"
        using add_closure e_proj_aff by auto

      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
          {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}"      
        (is "?s = ?c")
      proof(standard)
        show "?s \<subseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?s" 
          then obtain x1 y1 x2 y2 i j where
            "e = proj_add ((x1, y1), i) ((x2, y2), j)" 
            "((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)}"
            "((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
            "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1" by blast
          then have "e = (add (x, y) (x', y'), l + l') \<or> 
                     e = (\<tau> (add (x, y) (x', y')), l + l' + 1)" 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                aaa ds ds' ld_nz by fastforce
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then show "e \<in> ?s"
            using v1 v3 in_aff taus(1,2) 
                aaa ld_nz unfolding e_aff_0_def by force
        qed
      qed

      show "proj_addition ?p ?q = \<langle>(add (x,y) (x',y'),l+l')\<rangle>"
        unfolding proj_addition_def
        unfolding proj_add_class.simps(1)[OF assms(3,4)]
        unfolding assms
        using v1 v2 v3 v4 in_aff taus(1,2) 
              aaa ds ds' ld_nz
        apply(subst dom_eq) 
        apply(subst class_eq[symmetric])
        apply(subst eq_class_simp)
        using class_proj class_eq by auto
    next
      case bbb
      from bbb have v3: 
        "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (ext_add (x, y) (\<tau> (x', y')), l+l'+1)" 
        using proj_add.simps \<open>(x,y) \<in> e_aff\<close> \<open>(\<tau> (x', y')) \<in> e_aff\<close> by simp
      have pd: "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' = 0"
        using bbb unfolding delta_def delta_plus_def delta_minus_def
                           delta'_def delta_x_def delta_y_def 
        apply(simp add: t_nz nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)
        by(simp add: divide_simps t_nz nz)
      have pd': "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' \<noteq> 0"
        using bbb unfolding delta'_def delta_x_def delta_y_def
        by(simp add: t_nz nz divide_simps algebra_simps power2_eq_square[symmetric] t_expr d_nz)
      then have pd'': "delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0"
        unfolding delta'_def delta_x_def delta_y_def
        apply(simp add: divide_simps t_nz nz)
        by algebra
      have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (ext_add (\<tau> (x, y)) (x', y'), l+l'+1)"
        using proj_add.simps in_aff taus pd pd' by simp
      have v3_eq_v4: "(ext_add (x, y) (\<tau> (x', y')), l+l'+1) = (ext_add (\<tau> (x, y)) (x', y'), l+l'+1)" 
        using inversion_invariance_2 nz by auto
            
      have add_closure: "ext_add (x, y) (\<tau> (x', y')) \<in> e_aff"
      proof -
        obtain x1 y1 where z2_d: "\<tau> (x', y') = (x1,y1)" by fastforce
        define z3 where "z3 = ext_add (x,y) (x1,y1)"
        obtain x2 y2 where z3_d: "z3 = (x2,y2)" by fastforce
        have d': "delta' x y x1 y1 \<noteq> 0"
          using bbb z2_d by auto
        have "(x1,y1) \<in> e_aff"
          unfolding z2_d[symmetric]
          using \<open>\<tau> (x', y') \<in> e_aff\<close> by auto
        have e_eq: "e x y = 0" "e x1 y1 = 0"
          using \<open>(x,y) \<in> e_aff\<close> \<open>(x1,y1) \<in> e_aff\<close> unfolding e_aff_def by(auto)
          
        have "z3 \<in> e_aff"  
          using ext_add_closure in_aff(1) pd'' taus(1) z2_d z3_def by auto
        then show ?thesis 
          unfolding e_aff_def using z3_d z3_def z2_d by simp
      qed     

      have eq: "x * y' + y * x' \<noteq> 0"  "y * y' \<noteq> x * x'"
        using bbb unfolding delta'_def delta_x_def delta_y_def
        by(simp add: t_nz nz divide_simps)+

      have add_nz: "fst(ext_add (x, y) (\<tau> (x', y'))) \<noteq> 0"    
                   "snd(ext_add (x, y) (\<tau> (x', y'))) \<noteq> 0"
        apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr)
        apply(simp_all add: divide_simps d_nz t_nz nz)
        apply(safe)
        using ld_nz eq unfolding delta_def delta_minus_def delta_plus_def
        unfolding t_expr[symmetric]
        by algebra+
           
        have trans_add: "\<tau> (add (x, y) (x', y')) = (ext_add (x, y) (\<tau> (x', y')))" 
                        "add (x, y) (x', y') = \<tau> (ext_add (x, y) (\<tau> (x', y')))" 
        proof -
          show "\<tau> (add (x, y) (x', y')) = (ext_add (x, y) (\<tau> (x', y')))"
            using add_ext_add_2 nz(1) nz(2) v3_eq_v4 by fastforce
          then show "add (x, y) (x', y') = \<tau> (ext_add (x, y) (\<tau> (x', y')))" 
            using tau_idemp_point[of "add (x, y) (x', y')"] by argo 
        qed
        
      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
        {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}" 
      (is "?s = ?c")
      proof(standard)
        show "?s \<subseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?s" 
          then obtain x1 y1 x2 y2 i j where
            "e = proj_add ((x1, y1), i) ((x2, y2), j)" 
            "((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)}"
            "((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
            "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1" by blast
          then have "e = (add (x, y) (x', y'), l + l') \<or> 
                     e = (\<tau> (add (x, y) (x', y')), l + l' + 1)" 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                bbb ds  ld_nz 
            by (metis empty_iff insert_iff trans_add(1) v3_eq_v4)
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then have "e = (add (x, y) (x', y'), l + l') \<or> 
                     e = (\<tau> (add (x, y) (x', y')), l + l' + 1)" by blast
          then show "e \<in> ?s"
            apply(elim disjE)
            using v1 ld_nz in_aff unfolding e_aff_0_def apply force
            thm trans_add
            apply(subst (asm) trans_add)
            using v3 bbb in_aff taus unfolding e_aff_1_def by force
        qed
      qed

      have ext_eq: "gluing `` {(ext_add (x, y) (\<tau> (x', y')), l + l'+1)} =
            {(ext_add (x, y) (\<tau> (x', y')), l + l'+1), (\<tau> (ext_add (x, y) (\<tau> (x', y'))), l + l')}" 
        using add_nz add_closure gluing_class_2 by auto
      have class_eq: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> =
            {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}" 
      proof -
        have "\<langle>(add (x,y) (x',y'),l+l')\<rangle> =
              gluing `` {(\<tau> (ext_add (x, y) (\<tau> (x', y'))), l + l')}"
          using trans_add by argo
        also have "... = gluing `` {(ext_add (x, y) (\<tau> (x', y')), l + l'+1)}"
          using gluing_inv add_nz add_closure by auto
        also have "... = {(ext_add (x, y) (\<tau> (x', y')), l + l'+1), (\<tau> (ext_add (x, y) (\<tau> (x', y'))), l + l')}"
          using ext_eq by blast
        also have "... = {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}" 
          using trans_add by force
        finally show ?thesis by blast
      qed
       
      have ext_eq_proj: "gluing `` {(ext_add (x, y) (\<tau> (x', y')), l + l'+1)} \<in> e_proj"
        using add_closure e_proj_aff by auto
      then have class_proj: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> \<in> e_proj"
      proof -
        have "\<langle>(add (x,y) (x',y'),l+l')\<rangle> =
              gluing `` {(\<tau> (ext_add (x, y) (\<tau> (x', y'))), l + l')}"
          using trans_add by argo
        also have "... = gluing `` {(ext_add (x, y) (\<tau> (x', y')), l + l'+1)}"
          using gluing_inv add_nz add_closure by auto
        finally show ?thesis using ext_eq_proj by argo
      qed
 
      show ?thesis
        unfolding proj_addition_def
        unfolding proj_add_class.simps(1)[OF assms(3,4)]
        unfolding assms
        using v1 v2 v3 v4 in_aff taus(1,2) 
              bbb ds  ld_nz
        apply(subst dom_eq) 
        apply(subst class_eq[symmetric])
        apply(subst eq_class_simp)
        using class_proj class_eq by auto
    next
      case ccc
      then have v3: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = undefined" by simp 
      from ccc have ds': "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' = 0"
                     "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' = 0"
        unfolding delta_def delta_plus_def delta_minus_def
                  delta'_def delta_x_def delta_y_def 
        by(simp_all add: t_nz nz divide_simps algebra_simps power2_eq_square[symmetric] t_expr d_nz)   
      then have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = undefined" by simp 

      have add_z: "fst (add (x, y) (x', y')) = 0 \<or> snd (add (x, y) (x', y')) = 0"
        using b ccc unfolding e_aff_0_def 
                                 delta_def delta'_def delta_plus_def delta_minus_def
                                 delta_x_def delta_y_def e_aff_def e_def
        apply(simp add: t_nz nz field_simps)
        by algebra

      have add_closure: "add (x, y) (x', y') \<in> e_aff"
        using b(1) \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> add_closure 
        unfolding e_aff_0_def delta_def e_aff_def by simp
      have class_eq: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> = {(add (x, y) (x', y'), l + l')}"
        using add_z add_closure gluing_class_1 by simp
      have class_proj: "\<langle>(add (x,y) (x',y'),l+l')\<rangle> \<in> e_proj"
        using add_closure e_proj_aff by simp

      have dom_eq: 
        "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
         {(add (x, y) (x', y'), l + l')}"
        (is "?s = ?c")
      proof(standard)
        show "?s \<subseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?s" 
          then obtain x1 y1 x2 y2 i j where
            "e = proj_add ((x1, y1), i) ((x2, y2), j)" 
            "((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)}"
            "((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
            "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1" by blast
          then have "e = (add (x, y) (x', y'), l + l') " 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                  ld_nz ds ds' ccc
            unfolding e_aff_0_def e_aff_1_def by auto
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then have "e = (add (x, y) (x', y'), l + l')" by blast
          then show "e \<in> ?s"
            using v1 ld_nz in_aff unfolding e_aff_0_def by force
        qed
      qed
      show ?thesis
        unfolding proj_addition_def 
        unfolding proj_add_class.simps(1)[OF assms(3,4)]
        unfolding assms
        apply(subst dom_eq)
        apply(subst class_eq[symmetric])
        apply(subst eq_class_simp)
        using class_proj class_eq by auto
    qed
  next
    case c
    have "False"
      using c assms unfolding e_aff_1_def e_aff_0_def by simp
    then show ?thesis by simp
  qed
qed

lemma gluing_add:
  assumes "\<langle>((x1,y1),l)\<rangle> \<in> e_proj" "\<langle>((x2,y2),j)\<rangle> \<in> e_proj" "delta x1 y1 x2 y2 \<noteq> 0"
  shows "\<langle>((x1,y1),l)\<rangle> \<oplus> \<langle>((x2,y2),j)\<rangle> = \<langle>(add (x1,y1) (x2,y2),l+j)\<rangle>"
proof -
  have  p_q_expr: "(\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l)} \<or> \<langle>((x1,y1),l)\<rangle> = {((x1, y1), l), (\<tau> (x1, y1), l + 1)})" 
                  "(\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j)} \<or> \<langle>((x2,y2),j)\<rangle> = {((x2, y2), j), (\<tau> (x2, y2), j + 1)})"
    using assms(1,2) gluing_cases_explicit by auto
  then consider
           (1) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j)}" |
           (2) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" |
           (3) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j)}" |
           (4) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" by argo 
    then show ?thesis
    proof(cases)
      case 1 
      then show ?thesis using gluing_add_1 assms by presburger
    next
      case 2 then show ?thesis using gluing_add_2 assms by presburger
    next
      case 3 then show ?thesis
      proof -
        have pd: "delta x2 y2 x1 y1  \<noteq> 0" 
          using assms(3) unfolding delta_def delta_plus_def delta_minus_def
          by(simp,algebra)
        have add_com: "add (x2, y2) (x1, y1) = add (x1, y1) (x2, y2)"
          using add_comm by simp
        have "proj_addition (gluing `` {((x2, y2), j)}) (\<langle>((x1, y1), l)\<rangle>) =
              gluing `` {(add (x1, y1) (x2, y2), j + l)}"
          using gluing_add_2[OF 3(2) 3(1) assms(2) assms(1) pd] add_com 
          by simp
        then show ?thesis
          using proj_add_class_comm add.commute assms
          unfolding proj_addition_def by metis
      qed
    next
      case 4 then show ?thesis using gluing_add_4 assms by presburger
    qed
  qed  

lemma gluing_ext_add_1: 
  assumes "\<langle>((x,y),l)\<rangle> = {((x, y), l)}" "\<langle>((x',y'),l')\<rangle> = {((x', y'), l')}" 
          "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>((x',y'),l')\<rangle> \<in> e_proj" "delta' x y x' y' \<noteq> 0"
  shows "\<langle>((x,y),l)\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = (gluing `` {(ext_add (x,y) (x',y'),l+l')})"
proof -
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have zeros: "x = 0 \<or> y = 0" "x' = 0 \<or> y' = 0"
    using e_proj_elim_1 assms by simp+
  
  have ds: "delta' x y x' y' = 0" "delta' x y x' y' \<noteq> 0"     
      using delta'_def delta_x_def delta_y_def zeros(1) zeros(2) apply fastforce
      using assms(5) by simp
  consider
    (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
    (b) "((x, y), x', y') \<in> e_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
    (c) "((x, y), x', y') \<in> e_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e_aff_0"
    using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by argo
  then show ?thesis
  proof(cases)
    case a
    then have "False"
      using in_aff zeros unfolding e_circ_def by force
    then show ?thesis by simp
  next
    case b 
    from ds show ?thesis by simp
  next
    case c
    from ds show ?thesis by simp
  qed
qed

(*
 TODO: an interesting observation is that this proof is completely dual to the one for 
       add. In the sense, that the brances b and c are interchanged and the proofs only vary 
       on renaming. For instance, delta to delta'
*)
lemma gluing_ext_add_2:
  assumes "\<langle>((x,y),l)\<rangle> = {((x, y), l)}" "\<langle>((x',y'),l')\<rangle> = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" 
          "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>((x',y'),l')\<rangle> \<in> e_proj" "delta' x y x' y' \<noteq> 0"
  shows "\<langle>((x,y),l)\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = (gluing `` {(ext_add (x,y) (x',y'),l+l')})"
proof -
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have add_in: "ext_add (x, y) (x', y') \<in> e_aff"
    using ext_add_closure \<open>delta' x y x' y' \<noteq> 0\<close> delta_def e_aff_def by auto
  from in_aff have zeros: "x = 0 \<or> y = 0" "x' \<noteq> 0"  "y' \<noteq> 0"
    using e_proj_elim_1 e_proj_elim_2 assms apply(fastforce)
    using assms(2) assms(4) e_proj_elim_2 in_aff(2) by fastforce+
  have e_proj: "\<langle>((x,y),l)\<rangle> \<in> e_proj"
               "\<langle>((x',y'),l')\<rangle> \<in> e_proj"
               "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj"
    using e_proj_aff in_aff add_in by auto

  consider
      (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
      (b) "((x, y), x', y') \<in> e_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e_aff_1" |
      (c) "((x, y), x', y') \<in> e_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" 
      using dichotomy_1[OF \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>] by fast
  then show ?thesis
  proof(cases)
    case a
    then have "False"
      using in_aff zeros unfolding e_circ_def by force
    then show ?thesis by simp
  next
    case b
    have ld_nz: "delta' x y x' y' = 0" 
     using \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> b
     unfolding e_aff_1_def by force
    then have "False"
      using assms e_proj_elim_1 in_aff
      unfolding delta_def delta_minus_def delta_plus_def by blast
    then show ?thesis by blast
  next
   case c   
    then have ld_nz: "delta' x y x' y' \<noteq> 0" unfolding e_aff_1_def by auto    

    have v1: "proj_add ((x, y), l) ((x', y'), l') = (ext_add (x, y) (x', y'), l + l')"
      by(simp add: \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close>  ld_nz del: add.simps)

    have ecirc: "(x',y') \<in> e_circ" "x' \<noteq> 0" "y' \<noteq> 0"
      unfolding e_circ_def using zeros \<open>(x',y') \<in> e_aff\<close> by auto
    then have "\<tau> (x', y') \<in> e_circ" 
      using zeros \<tau>_circ by blast
    then have in_aff': "\<tau> (x', y') \<in> e_aff"
      unfolding e_circ_def by force

    have add_nz: "fst (ext_add (x, y) (x', y')) \<noteq> 0" 
                 "snd (ext_add (x, y) (x', y')) \<noteq> 0" 
      using zeros ld_nz in_aff
      unfolding delta_def delta_plus_def delta_minus_def e_aff_def e_def
      apply(simp_all)
      by auto

    have add_in: "ext_add (x, y) (x', y') \<in> e_aff"
      using ext_add_closure in_aff ld_nz unfolding e_aff_def delta_def by simp

    have ld_nz': "delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
      using ld_nz
      unfolding delta'_def delta_x_def delta_y_def
      using zeros by(auto simp add: divide_simps t_nz) 
    
    have tau_conv: "\<tau> (ext_add (x, y) (x', y')) = ext_add (x, y) (\<tau> (x', y'))"
      using zeros e_aff_x0[OF _ in_aff(1)] e_aff_y0[OF _ in_aff(1)] 
      apply(simp_all)
      apply(simp_all add: divide_simps d_nz t_nz)
      apply(elim disjE) 
      apply(simp_all add: t_nz zeros) 
      by auto

    have v2: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (ext_add (x, y) (x', y')), l+l'+1)"
      using proj_add.simps \<open>\<tau> (x', y') \<in> e_aff\<close> in_aff tau_conv 
            \<open>delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0\<close> by auto    
     
    have gl_class: "gluing `` {(ext_add (x, y) (x', y'), l + l')} =
                {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}"
           "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj" 
      using gluing_class_2 add_nz add_in apply simp
      using e_proj_aff add_in by auto
   
    show ?thesis          
    proof -
      have "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and>
       ((x1, y1), x2, y2)
       \<in> e_aff_0 \<union> {((x1, y1), x2, y2). (x1, y1) \<in> e_aff \<and> (x2, y2) \<in> e_aff \<and> delta' x1 y1 x2 y2 \<noteq> 0}} =
      {proj_add ((x, y), l) ((x', y'), l'), proj_add ((x, y), l) (\<tau> (x', y'), l' + 1)}"
        (is "?t = _")
        using ld_nz ld_nz' in_aff in_aff' 
        apply(simp del: \<tau>.simps add.simps) 
        by force
      also have "... = {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}"
        using v1 v2 by presburger
      finally have eq: "?t = {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}"
        by blast
    
      show ?thesis
       unfolding proj_addition_def
       unfolding proj_add_class.simps(1)[OF e_proj(1,2)]
       unfolding assms(1,2) gl_class e_aff_1_def
       apply(subst eq)
       apply(subst eq_class_simp)
       using gl_class by auto
   qed
  qed    
qed    


lemma gluing_ext_add_4:
 assumes "\<langle>((x,y),l)\<rangle> = {((x, y), l), (\<tau> (x, y), l + 1)}" "\<langle>((x',y'),l')\<rangle> = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" 
          "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>((x',y'),l')\<rangle> \<in> e_proj" "delta' x y x' y' \<noteq> 0"
  shows "\<langle>((x,y),l)\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = (gluing `` {(ext_add (x,y) (x',y'),l+l')})"
 (is "proj_addition ?p ?q = _")
proof -
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"
    using e_proj_aff assms by meson+
  then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
    using assms e_proj_elim_2 apply(fastforce,fastforce)
    using assms(2) assms(4) e_proj_elim_2 in_aff(2) by fastforce+
  then have circ: "(x,y) \<in> e_circ" "(x',y') \<in> e_circ"
    using in_aff e_circ_def nz by auto
  then have taus: "(\<tau> (x', y')) \<in> e_aff" "(\<tau> (x, y)) \<in> e_aff" "\<tau> (x', y') \<in> e_circ"
    using \<tau>_circ circ_to_aff by auto

  consider 
   (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (b) "((x, y), x', y') \<in> e_aff_0" "((x, y), x', y') \<notin> e_aff_1" 
   | (c) "((x, y), x', y') \<in> e_aff_1" 
    using dichotomy_1[OF in_aff] by auto
  then show ?thesis
  proof(cases)
    case a 
    then obtain g where sym_expr: "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" by auto        
    then have ds: "delta x y x' y' = 0" "delta' x y x' y' = 0"
      using wd_d_nz wd_d'_nz a by auto 
    then have "False" 
      using assms by auto
    then show ?thesis by blast    
  next
    case b
    have "False"
      using b assms unfolding e_aff_1_def e_aff_0_def by simp
    then show ?thesis by simp
  next
    case c
    then have ld_nz: "delta' x y x' y' \<noteq> 0" 
      unfolding e_aff_1_def by auto    
    then have ds: "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" 
      unfolding delta'_def delta_x_def delta_y_def 
      (*TODO: note how field_simps is preferable over divide_simps in the field generalization*)
      by(simp add: t_nz field_simps nz)
      
    have v1: "proj_add ((x, y), l) ((x', y'), l') = (ext_add (x, y) (x', y'), l + l')"
      using ld_nz proj_add.simps \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> by simp
    have v2: "proj_add (\<tau> (x, y), l+1) (\<tau> (x', y'), l'+1) = (ext_add (x, y) (x', y'), l + l')"
      apply(subst proj_add.simps(2)[OF ds,simplified prod.collapse taus(2) taus(1)])
       apply simp
      apply(simp del: ext_add.simps \<tau>.simps)
      apply(rule inversion_invariance_2[of "(x,y)" "(\<tau> (x',y'))",simplified prod.collapse tau_idemp_point])
      using nz t_nz by auto

    consider (aaa) "delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" |
             (bbb) "delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" 
                   "delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) = 0" |
             (ccc) "delta' x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) = 0" 
                   "delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) = 0" by blast
    then show ?thesis
    proof(cases)
      case aaa
      have tau_conv: "\<tau> (ext_add (x, y) (\<tau> (x', y'))) = ext_add (x,y) (x',y')"
        apply(simp)
        using aaa in_aff ld_nz 
        unfolding e_aff_def e_def delta'_def delta_x_def delta_y_def 
        apply(safe)
         apply(simp_all add: divide_simps t_nz nz)
        by algebra+
      
      have v3: 
        "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (ext_add (x, y) (x', y')), l+l'+1)" 
        using proj_add.simps \<open>(\<tau> (x', y')) \<in> e_aff\<close> 
        apply(simp del: ext_add.simps \<tau>.simps)
        using tau_conv tau_idemp_explicit 
              proj_add.simps(2)[OF aaa \<open>(x,y) \<in> e_aff\<close>,simplified prod.collapse,OF \<open>(\<tau> (x', y')) \<in> e_aff\<close>] 
        by (metis (no_types, lifting) add.assoc prod.collapse)

      have ds': "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' \<noteq> 0"
        using aaa unfolding delta'_def delta_x_def delta_y_def
        by(simp add: divide_simps t_nz nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)

      have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (\<tau> (ext_add (x, y) (x', y')), l+l'+1)"
      proof -
        have "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (ext_add (\<tau> (x, y)) (x', y'), l+l'+1)" 
          using proj_add.simps \<open>\<tau> (x,y) \<in> e_aff\<close> \<open>(x', y') \<in> e_aff\<close> ds' by auto
        moreover have "ext_add (\<tau> (x, y)) (x', y') = \<tau> (ext_add (x, y) (x', y'))"
          by (metis inversion_invariance_2 nz tau_conv tau_idemp_point fst_conv snd_conv)
        ultimately show ?thesis by argo          
      qed  

      have add_closure: "ext_add (x,y) (x',y') \<in> e_aff"
        using in_aff ext_add_closure ld_nz unfolding delta'_def e_aff_def by auto

      have add_nz: "fst (ext_add (x,y) (x',y')) \<noteq> 0"
                   "snd (ext_add (x,y) (x',y')) \<noteq> 0"
        using ld_nz unfolding delta_def delta_minus_def   
        apply(simp_all)
        using aaa in_aff ld_nz unfolding e_aff_def e_def delta'_def delta_x_def delta_y_def 
        apply(simp_all add: t_expr nz t_nz divide_simps)
        apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr d_nz) 
        by algebra+

      have class_eq: "gluing `` {(ext_add (x, y) (x', y'), l + l')} =
            {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}" 
        using add_nz add_closure gluing_class_2 by auto
      have class_proj: "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj"
        using add_closure e_proj_aff by auto

      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
          {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}"      
        (is "?s = ?c")
      proof(standard)
        show "?s \<subseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?s" 
          then obtain x1 y1 x2 y2 i j where
            "e = proj_add ((x1, y1), i) ((x2, y2), j)" 
            "((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)}"
            "((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
            "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1" by blast
          then have "e = (ext_add (x, y) (x', y'), l + l') \<or> 
                     e = (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)" 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                aaa ds ds' ld_nz by fastforce
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then show "e \<in> ?s"
            using v1 v3 in_aff taus(1,2) 
                aaa ld_nz unfolding e_aff_1_def by force
        qed
      qed

      show "proj_addition ?p ?q = gluing `` {(ext_add (x, y) (x', y'), l + l')}"
        unfolding proj_addition_def
        unfolding proj_add_class.simps(1)[OF assms(3,4)]
        unfolding assms
        using v1 v2 v3 v4 in_aff taus(1,2) 
              aaa ds ds' ld_nz
        apply(subst dom_eq) 
        apply(subst class_eq[symmetric])
        apply(subst eq_class_simp)
        using class_proj class_eq by auto
    next
      case bbb
      from bbb have v3: 
        "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (add (x, y) (\<tau> (x', y')), l+l'+1)" 
        using proj_add.simps \<open>(x,y) \<in> e_aff\<close> \<open>(\<tau> (x', y')) \<in> e_aff\<close> by simp
      have pd: "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' = 0"
        using bbb unfolding delta_def delta_plus_def delta_minus_def
                           delta'_def delta_x_def delta_y_def 
        apply(simp add: divide_simps t_nz nz)
        apply(simp add: t_nz nz algebra_simps power2_eq_square[symmetric] t_expr d_nz) 
        by presburger
      have pd': "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' \<noteq> 0"
        using bbb unfolding delta'_def delta_x_def delta_y_def
                            delta_def delta_plus_def delta_minus_def 
        by(simp add: t_nz nz field_simps power2_eq_square[symmetric] t_expr d_nz)
      then have pd'': "delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0"
        unfolding delta_def delta_plus_def delta_minus_def
        by(simp add: divide_simps t_nz nz algebra_simps t_expr power2_eq_square[symmetric] d_nz)
      have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (add (\<tau> (x, y)) (x', y'), l+l'+1)"
        using proj_add.simps in_aff taus pd pd' by auto
      have v3_eq_v4: "(add (x, y) (\<tau> (x', y')), l+l'+1) = (add (\<tau> (x, y)) (x', y'), l+l'+1)" 
        using inversion_invariance_1 nz by auto
            
      have add_closure: "add (x, y) (\<tau> (x', y')) \<in> e_aff"
      proof -
        obtain x1 y1 where z2_d: "\<tau> (x', y') = (x1,y1)" by fastforce
        define z3 where "z3 = add (x,y) (x1,y1)"
        obtain x2 y2 where z3_d: "z3 = (x2,y2)" by fastforce
        have d': "delta x y x1 y1 \<noteq> 0"
          using bbb z2_d by auto
        have "(x1,y1) \<in> e_aff"
          unfolding z2_d[symmetric]
          using \<open>\<tau> (x', y') \<in> e_aff\<close> by auto
        have e_eq: "e x y = 0" "e x1 y1 = 0"
          using \<open>(x,y) \<in> e_aff\<close> \<open>(x1,y1) \<in> e_aff\<close> unfolding e_aff_def by(auto)
          
        have "z3 \<in> e_aff" 
          using add_closure in_aff(1) pd'' taus(1) z2_d z3_def by auto
        then show ?thesis 
          unfolding e_aff_def using z3_d z3_def z2_d by simp
      qed     

      have add_nz: "fst(add (x, y) (\<tau> (x', y'))) \<noteq> 0"    
                   "snd(add (x, y) (\<tau> (x', y'))) \<noteq> 0"
        apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr)
        apply(simp_all add: divide_simps d_nz t_nz nz)
         apply(safe)
        using bbb ld_nz unfolding delta'_def delta_x_def delta_y_def
                            delta_def delta_plus_def delta_minus_def 
        by(simp_all add: divide_simps t_nz nz algebra_simps 
                              power2_eq_square[symmetric] t_expr d_nz)

           
        have trans_add: "\<tau> (ext_add (x, y) (x', y')) = (add (x, y) (\<tau> (x', y')))" 
                        "ext_add (x, y) (x', y') = \<tau> (add (x, y) (\<tau> (x', y')))" 
        proof -
          show "\<tau> (ext_add (x, y) (x', y')) = (add (x, y) (\<tau> (x', y')))" 
            using inversion_invariance_1 assms add_ext_add nz tau_idemp_point by force          then show "ext_add (x, y) (x', y') = \<tau> (add (x, y) (\<tau> (x', y')))"  
            using tau_idemp_point[of "ext_add (x, y) (x', y')"] by argo
        qed
        
      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
        {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}" 
      (is "?s = ?c")
      proof(standard)
        show "?s \<subseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?s" 
          then obtain x1 y1 x2 y2 i j where
            "e = proj_add ((x1, y1), i) ((x2, y2), j)" 
            "((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)}"
            "((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
            "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1" by blast
          then have "e = (ext_add (x, y) (x', y'), l + l') \<or> 
                     e = (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)" 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                bbb ds ld_nz 
            by (metis empty_iff insert_iff trans_add(1) v3_eq_v4)
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then have "e = (ext_add (x, y) (x', y'), l + l') \<or> 
                     e = (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)" by blast
          then show "e \<in> ?s"
            apply(elim disjE)
            using v1 ld_nz in_aff unfolding e_aff_1_def apply force
            apply(subst (asm) trans_add)
            using v3 bbb in_aff taus unfolding e_aff_0_def by force
        qed
      qed

      have ext_eq: "gluing `` {(add (x, y) (\<tau> (x', y')), l + l'+1)} =
            {(add (x, y) (\<tau> (x', y')), l + l'+1), (\<tau> (add (x, y) (\<tau> (x', y'))), l + l')}" 
        using add_nz add_closure gluing_class_2 by auto
      have class_eq: "gluing `` {(ext_add (x, y) (x', y'), l + l')} =
            {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}" 
      proof -
        have "gluing `` {(ext_add (x, y) (x', y'), l + l')} =
              gluing `` {(\<tau> (add (x, y) (\<tau> (x', y'))), l + l')}"
          using trans_add by argo
        also have "... = gluing `` {(add (x, y) (\<tau> (x', y')), l + l'+1)}"
          using gluing_inv add_nz add_closure by auto
        also have "... = {(add (x, y) (\<tau> (x', y')), l + l'+1), (\<tau> (add (x, y) (\<tau> (x', y'))), l + l')}"
          using ext_eq by blast
        also have "... = {(ext_add (x, y) (x', y'), l + l'), (\<tau> (ext_add (x, y) (x', y')), l + l' + 1)}" 
          using trans_add by force
        finally show ?thesis by blast
      qed
       
      have ext_eq_proj: "gluing `` {(add (x, y) (\<tau> (x', y')), l + l'+1)} \<in> e_proj"
        using add_closure e_proj_aff by auto
      then have class_proj: "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj"
      proof -
        have "gluing `` {(ext_add (x, y) (x', y'), l + l')} =
              gluing `` {(\<tau> (add (x, y) (\<tau> (x', y'))), l + l')}"
          using trans_add by argo
        also have "... = gluing `` {(add (x, y) (\<tau> (x', y')), l + l'+1)}"
          using gluing_inv add_nz add_closure by auto
        finally show ?thesis using ext_eq_proj by argo
      qed
 
      show ?thesis
        unfolding proj_addition_def
        unfolding proj_add_class.simps(1)[OF assms(3,4)]
        unfolding assms
        using v1 v2 v3 v4 in_aff taus(1,2) 
              bbb ds  ld_nz
        apply(subst dom_eq) 
        apply(subst class_eq[symmetric])
        apply(subst eq_class_simp)
        using class_proj class_eq by auto
    next
      case ccc
      then have v3: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = undefined" by simp 
      from ccc have ds': "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' = 0"
                     "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' = 0"
        unfolding delta_def delta_plus_def delta_minus_def
                  delta'_def delta_x_def delta_y_def 
        by(simp_all add: t_nz nz divide_simps algebra_simps power2_eq_square[symmetric] t_expr d_nz)
      then have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = undefined" by simp 

      have add_z: "fst (ext_add (x, y) (x', y')) = 0 \<or> snd (ext_add (x, y) (x', y')) = 0"
        using c ccc ld_nz unfolding e_aff_0_def
                                 delta_def delta'_def delta_plus_def delta_minus_def
                                 delta_x_def delta_y_def e_aff_def e_def
        apply(simp_all add: field_simps t_nz nz)
        unfolding t_expr[symmetric] power2_eq_square 
        apply(simp_all add: divide_simps d_nz t_nz) 
        by algebra

      have add_closure: "ext_add (x, y) (x', y') \<in> e_aff"
        using c(1) \<open>(x,y) \<in> e_aff\<close> \<open>(x',y') \<in> e_aff\<close> ext_add_closure 
        unfolding e_aff_1_def delta_def e_aff_def by simp
      have class_eq: "gluing `` {(ext_add (x, y) (x', y'), l + l')} = {(ext_add (x, y) (x', y'), l + l')}"
        using add_z add_closure gluing_class_1 by simp
      have class_proj: "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj"
        using add_closure e_proj_aff by simp

      have dom_eq: 
        "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1} = 
         {(ext_add (x, y) (x', y'), l + l')}"
        (is "?s = ?c")
      proof(standard)
        show "?s \<subseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?s" 
          then obtain x1 y1 x2 y2 i j where
            "e = proj_add ((x1, y1), i) ((x2, y2), j)" 
            "((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)}"
            "((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
            "((x1, y1), x2, y2) \<in> e_aff_0 \<union> e_aff_1" by blast
          then have "e = (ext_add (x, y) (x', y'), l + l') " 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                  ld_nz ds ds' ccc
            unfolding e_aff_0_def e_aff_1_def 
            by fastforce
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then have "e = (ext_add (x, y) (x', y'), l + l')" by blast
          then show "e \<in> ?s"
            using v1 ld_nz in_aff unfolding e_aff_1_def by force
        qed
      qed
      show ?thesis
        unfolding proj_addition_def 
        unfolding proj_add_class.simps(1)[OF assms(3,4)]
        unfolding assms
        apply(subst dom_eq)
        apply(subst class_eq[symmetric])
        apply(subst eq_class_simp)
        using class_proj class_eq by auto
    qed
  qed
qed

lemma gluing_ext_add:
  assumes "\<langle>((x1,y1),l)\<rangle> \<in> e_proj" "\<langle>((x2,y2),j)\<rangle> \<in> e_proj" "delta' x1 y1 x2 y2 \<noteq> 0"
  shows "\<langle>((x1,y1),l)\<rangle> \<oplus> \<langle>((x2,y2),j)\<rangle> = \<langle>(ext_add (x1,y1) (x2,y2),l+j)\<rangle>"
proof -
  have  p_q_expr: "(\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l)} \<or> \<langle>((x1,y1),l)\<rangle> = {((x1, y1), l), (\<tau> (x1, y1), l + 1)})" 
                  "(\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j)} \<or> \<langle>((x2,y2),j)\<rangle> = {((x2, y2), j), (\<tau> (x2, y2), j + 1)})"
    using assms(1,2) gluing_cases_explicit by auto
  then consider
           (1) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j)}" |
           (2) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" |
           (3) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j)}" |
           (4) "\<langle>((x1,y1),l)\<rangle> = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "\<langle>((x2,y2),j)\<rangle> = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" by argo 
    then show ?thesis
    proof(cases)
      case 1 
      then show ?thesis using gluing_ext_add_1 assms by presburger
    next
      case 2 then show ?thesis using gluing_ext_add_2 assms by presburger
    next
      case 3 then show ?thesis
      proof -
        have pd: "delta' x2 y2 x1 y1 \<noteq> 0"
          using assms(3) unfolding delta'_def delta_x_def delta_y_def by algebra
        have "proj_addition (\<langle>((x1, y1), l)\<rangle>) (gluing `` {((x2, y2), j)}) = 
              proj_addition (gluing `` {((x2, y2), j)}) (\<langle>((x1, y1), l)\<rangle>)"
          unfolding proj_addition_def
          apply(subst proj_add_class_comm[OF ])
          using assms by auto
        also have "... = gluing `` {(ext_add (x2, y2) (x1, y1), j+l)}"
          using gluing_ext_add_2[OF 3(2,1) assms(2,1) pd] by blast
        also have "... = gluing `` {(ext_add (x1, y1) (x2, y2), l+j)}"
          by (metis add.commute ext_add_comm)
        finally show ?thesis by fast
      qed
    next
      case 4 then show ?thesis using gluing_ext_add_4 assms by presburger
    qed
  qed  

lemma independence:
  assumes "\<langle>((x1,y1),l1)\<rangle> \<in> e_proj" "\<langle>((x2,y2),l2)\<rangle> \<in> e_proj" 
  shows "\<langle>((x1,y1),l1)\<rangle> \<oplus> \<langle>((x2,y2),l2)\<rangle> = \<langle>proj_add' ((x1,y1),l1) ((x2,y2),l2)\<rangle>"
  (is "?c1 \<oplus> ?c2 = ?c3")
proof -
  have in_aff:"(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff"
    using assms e_proj_aff by blast+    
  have "delta x1 y1 x2 y2 \<noteq> 0 \<or> delta' x1 y1 x2 y2 \<noteq> 0 \<or>
        delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0 \<or>
        delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0"
    using covering_with_deltas in_aff by auto

  then consider 
    (a) "delta x1 y1 x2 y2 \<noteq> 0" |
    (b) "delta' x1 y1 x2 y2 \<noteq> 0" |
    (c) "delta x1 y1 x2 y2 = 0"
        "delta' x1 y1 x2 y2 = 0"
        "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" |
    (d) "delta x1 y1 x2 y2 = 0"
        "delta' x1 y1 x2 y2 = 0"
        "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" by auto
  then show ?thesis
  proof(cases)
    case a
    then show ?thesis 
      using assms(1) assms(2) e_proj_aff gluing_add by auto
  next
    case b
    then show ?thesis
      using assms(1) assms(2) e_proj_aff gluing_ext_add by auto
  next
    case c   
    have "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
         "delta' (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
      using assms(1) assms(2) c(1) e_proj_aff tau_tau_d apply blast
      using assms(1) assms(2) c(2) e_proj_aff tau_tau_d' by blast
    then have nt_in_class: "\<not>(((x1,y1), x2, y2) \<in> e_aff_0 \<or> ((x1,y1), x2, y2) \<in> e_aff_1)"
                      "\<not>((\<tau> (x1,y1), \<tau> (x2,y2)) \<in> e_aff_0 \<or> (\<tau> (x1,y1), \<tau> (x2,y2)) \<in> e_aff_1)"
      unfolding e_aff_0_def e_aff_1_def
      by(auto simp add: c(1) c(2))

    have class_eq:
         "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1), (\<tau> (x1,y1),l1+1)} \<or> \<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)}"
         "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2), (\<tau> (x2,y2),l2+1)} \<or> \<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)}"
      using assms gluing_cases_explicit by blast+
    have "\<not> (\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)} \<and> \<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)})"
    proof(rule ccontr)
      assume "\<not> \<not> (gluing `` {((x1, y1), l1)} = {((x1, y1), l1)} \<and> gluing `` {((x2, y2), l2)} = {((x2, y2), l2)})"
      then have "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)}" "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)}" by auto
      then have "proj_add_class \<langle>((x1,y1),l1)\<rangle> \<langle>((x2,y2),l2)\<rangle> = {}"
        using assms apply simp
        unfolding e_aff_0_def e_aff_1_def apply simp
        using c by blast
      then show "False"
        using assms(1) assms(2) covering by blast
    qed
    then consider
      (aa) "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1), (\<tau> (x1,y1),l1+1)}"
           "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)}" |
      (bb) "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)}"
           "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2), (\<tau> (x2,y2),l2+1)}" | 
      (cc) "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1), (\<tau> (x1,y1),l1+1)}"
           "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2), (\<tau> (x2,y2),l2+1)}"  
      using class_eq by argo
    then show ?thesis
    proof(cases)
      case aa
      have nz: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 = 0 \<or> y2 = 0"
        using aa(1) assms(1) e_proj_elim_2 in_aff(1) apply(fastforce,fastforce)
        using aa assms e_proj_elim_1 e_proj_elim_2 in_aff by auto

      have "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
           "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
        subgoal
          using c(1) \<open>x2 = 0 \<or> y2 = 0\<close> 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        subgoal
          using c(1) \<open>x2 = 0 \<or> y2 = 0\<close> 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        done

      have eq: "{proj_add ((x1a, y1a), i) ((x2, y2), l2) |x1a y1a i.
                 (((x1a,y1a),i) = ((x1,y1),l1) \<or> ((x1a,y1a),i) = (\<tau> (x1, y1),l1+1))
                 \<and> (((x1a, y1a), x2, y2) \<in> e_aff_0 \<or> ((x1a, y1a), x2, y2) \<in> e_aff_1)} = 
             {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        (is "?s1 = ?s2")
      proof(intro equalityI,standard)
        fix s
        assume "s \<in> ?s1"
        then have "s = proj_add (\<tau> (x1,y1),l1+1) ((x2, y2), l2)"
          using nt_in_class by auto
        then show "s \<in> ?s2"
          by blast
      next 
        show "?s2 \<subseteq> ?s1"
        proof(standard)
          fix s
          assume "s \<in> ?s2"
          then have "s = proj_add (\<tau> (x1, y1), l1 + 1) ((x2, y2), l2)"
            by auto
          then show "s \<in> ?s1"
            using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by blast      
        qed
      qed
       
      have "proj_add_class ?c1 ?c2 =
             {proj_add ((x1a, y1a), i) ((x2, y2), l2) |x1a y1a i. 
                 (((x1a,y1a),i) = ((x1,y1),l1) \<or> ((x1a,y1a),i) = (\<tau> (x1, y1),l1+1))
                 \<and> (((x1a, y1a), x2, y2) \<in> e_aff_0 \<or> ((x1a, y1a), x2, y2) \<in> e_aff_1)} // gluing"
        using aa assms by(simp del: \<tau>.simps)
      also have "... =  {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)} // gluing"
        using eq by auto
      finally have eq': "proj_add_class ?c1 ?c2 = {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)} // gluing" by auto
      then have "?c1 \<oplus> ?c2 = {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        unfolding proj_addition_def eq' 
        using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by blast
      have " gluing `` {proj_add' ((x1, y1), l1) ((x2, y2), l2)} =  {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by blast
      then show ?thesis
        using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by linarith
    next
      case bb (* symmetric *)
      have nz: "x2 \<noteq> 0" "y2 \<noteq> 0" "x1 = 0 \<or> y1 = 0"
        using assms(2) bb(2) e_proj_elim_2 in_aff(2) apply(fastforce,fastforce)
        using assms(1) bb(1) e_proj_elim_1 in_aff(1) by auto

      have "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
           "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
        subgoal
          using c(1) nz 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        subgoal
          using c(1) nz 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        done

      have eq: "{proj_add ((x1,y1),l1) ((x1a,y1a),i) |x1a y1a i. 
                 (((x1a,y1a),i) = ((x2,y2),l2) \<or> ((x1a,y1a),i) = (\<tau> (x2, y2),l2+1))
                 \<and> (((x1,y1), (x1a,y1a)) \<in> e_aff_0 \<or> ((x1,y1), (x1a,y1a)) \<in> e_aff_1)} = 
             {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)}"
        (is "?s1 = ?s2")
      proof(intro equalityI,standard)
        fix s
        assume "s \<in> ?s1"
        then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)"
          using nt_in_class by auto
        then show "s \<in> ?s2"
          by blast
      next 
        show "?s2 \<subseteq> ?s1"
        proof(standard)
          fix s
          assume "s \<in> ?s2"
          then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)"
            by auto
          then show "s \<in> ?s1"
            using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by blast      
        qed
      qed
       
      have "proj_add_class ?c1 ?c2 =
             {proj_add ((x1,y1),l1) ((x1a,y1a),i) |x1a y1a i. 
                 (((x1a,y1a),i) = ((x2,y2),l2) \<or> ((x1a,y1a),i) = (\<tau> (x2, y2),l2+1))
                 \<and> (((x1,y1), (x1a,y1a)) \<in> e_aff_0 \<or> ((x1,y1), (x1a,y1a)) \<in> e_aff_1)} // gluing"
        using bb assms by(simp del: \<tau>.simps)
      also have "... =  {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)} // gluing"
        using eq by auto
      finally have eq': "proj_add_class ?c1 ?c2 = {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)} // gluing" by auto
      then have "?c1 \<oplus> ?c2 = {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)}"
        unfolding proj_addition_def eq' 
        using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by blast
      have " gluing `` {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)} =  {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by blast
      then show ?thesis
        using \<open>delta x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> c(3) by linarith
    next
      case cc
       have nz: "x2 \<noteq> 0" "y2 \<noteq> 0" "x1 \<noteq> 0" "y1 \<noteq> 0"
         using c(1) delta_def delta_minus_def delta_plus_def by auto

      have "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0"
        using c(3) by linarith
      have "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) x2 y2 \<noteq> 0"
        by (metis \<tau>.simps assms(1) c(3) e_proj_aff fst_conv gluing_inv in_aff(2) nz(3) nz(4) snd_conv tau_idemp_point tau_tau_d)
      have rev: "proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1) = proj_add (\<tau> (x1, y1), l1+1) ((x2, y2), l2)"
      proof -
        have "l1 + (l2 + 1) = l1 + 1 + l2" by simp
        then show ?thesis
          by (metis (no_types) \<open>delta (fst (\<tau> (x1, y1))) (snd (\<tau> (x1, y1))) x2 y2 \<noteq> 0\<close> assms(2) c(3) 
                  ext_curve_addition.e_proj_aff ext_curve_addition_axioms gluing_inv in_aff(1) inversion_invariance_1 
                  nz(1) nz(2) nz(3) nz(4) prod.collapse proj_add.simps(1) fst_conv snd_conv)
      qed

      have eq: "{proj_add ((x, y), i) ((x', y'), j) | 
              x y i x' y' j. 
              ((x, y), i) \<in> ?c1 \<and> 
              ((x', y'), j) \<in> ?c2 \<and> 
              ((x, y), (x', y')) \<in> e_aff_0 \<union> e_aff_1} = 
            {proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)}"
         (is "?s1 = ?s2")
      proof(intro equalityI;standard)
        fix s
        assume "s \<in> ?s1"
        then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1) \<or> 
                   s = proj_add (\<tau> (x1, y1), l1+1) ((x2, y2), l2)"
          apply(simp del: \<tau>.simps)
          using nt_in_class 
          by (metis gluing_char)
        then show "s \<in> ?s2"
          using rev by auto
      next 
        fix s
        assume "s \<in> ?s2"
        then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)"
          by auto
        then show "s \<in> ?s1"
        proof -
          have "((x1,y1),\<tau> (x2,y2)) \<in> e_aff_0"
            unfolding e_aff_0_def apply(simp del: \<tau>.simps)
            by (metis (mono_tags, lifting) assms(2) c(3) e_proj_aff gluing_inv in_aff(1) nz(1) nz(2) prod.case_eq_if prod.collapse)
          have "(((x2, y2), l2), (\<tau> (x2, y2), l2+1)) \<in> gluing"
            using cc(2) by auto
          then show ?thesis
            apply(simp del: \<tau>.simps)
            using \<open>((x1, y1), \<tau> (x2, y2)) \<in> e_aff_0\<close> \<open>s = proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2 + 1)\<close> cc(1) by fastforce
        qed
      qed     
      
      have "proj_add_class ?c1 ?c2 =
             {proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)} // gluing"
        using assms eq by auto
      then have "?c1 \<oplus> ?c2 =
             \<langle>proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)\<rangle>"
      proof -
        have "proj_add_class ?c1 ?c2 \<noteq> {}"
          using assms(1) assms(2) covering by blast
        then have "?c1 \<oplus> ?c2 = \<langle>proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)\<rangle>"
          by (simp add: \<open>proj_add_class (gluing `` {((x1, y1), l1)}) (gluing `` {((x2, y2), l2)}) = {proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2 + 1)} // gluing\<close> proj_addition_def singleton_quotient)
        then show ?thesis by auto
      qed
      have "proj_add' ((x1, y1), l1) ((x2, y2), l2) = proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)"
        using c by(simp del: \<tau>.simps)
      then show ?thesis 
        by (simp add: \<open>\<langle>((x1, y1), l1)\<rangle> \<oplus> \<langle>((x2, y2), l2)\<rangle> = \<langle>proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2 + 1)\<rangle>\<close>)
    qed    
  next
    case d
    have "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
         "delta' (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
      using assms(1) assms(2) d(1) e_proj_aff tau_tau_d apply blast
      using assms(1) assms(2) d(2) e_proj_aff tau_tau_d' by blast
    then have nt_in_class: "\<not>(((x1,y1), x2, y2) \<in> e_aff_0 \<or> ((x1,y1), x2, y2) \<in> e_aff_1)"
                      "\<not>((\<tau> (x1,y1), \<tau> (x2,y2)) \<in> e_aff_0 \<or> (\<tau> (x1,y1), \<tau> (x2,y2)) \<in> e_aff_1)"
      unfolding e_aff_0_def e_aff_1_def
      by(auto simp add: d(1) d(2))

    have class_eq:
         "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1), (\<tau> (x1,y1),l1+1)} \<or> \<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)}"
         "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2), (\<tau> (x2,y2),l2+1)} \<or> \<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)}"
      using assms gluing_cases_explicit by blast+
    have "\<not> (\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)} \<and> \<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)})"
    proof(rule ccontr)
      assume "\<not> \<not> (gluing `` {((x1, y1), l1)} = {((x1, y1), l1)} \<and> gluing `` {((x2, y2), l2)} = {((x2, y2), l2)})"
      then have "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)}" "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)}" by auto
      then have "proj_add_class \<langle>((x1,y1),l1)\<rangle> \<langle>((x2,y2),l2)\<rangle> = {}"
        using assms apply simp
        unfolding e_aff_0_def e_aff_1_def apply simp
        using d by blast
      then show "False"
        using assms(1) assms(2) covering by blast
    qed
    then consider
      (aa) "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1), (\<tau> (x1,y1),l1+1)}"
           "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2)}" |
      (bb) "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1)}"
           "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2), (\<tau> (x2,y2),l2+1)}" | 
      (cc) "\<langle>((x1,y1),l1)\<rangle> = {((x1,y1),l1), (\<tau> (x1,y1),l1+1)}"
           "\<langle>((x2,y2),l2)\<rangle> = {((x2,y2),l2), (\<tau> (x2,y2),l2+1)}"  
      using class_eq by argo
    then show ?thesis
    proof(cases)
      case aa
      have nz: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 = 0 \<or> y2 = 0"
        using aa assms e_proj_elim_1 e_proj_elim_2 in_aff by fastforce+

      have "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
           "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
        subgoal
          using d(1) nz 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        subgoal
          using d(1) nz
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        done

      have eq: "{proj_add ((x1a, y1a), i) ((x2, y2), l2) |x1a y1a i.
                 (((x1a,y1a),i) = ((x1,y1),l1) \<or> ((x1a,y1a),i) = (\<tau> (x1, y1),l1+1))
                 \<and> (((x1a, y1a), x2, y2) \<in> e_aff_0 \<or> ((x1a, y1a), x2, y2) \<in> e_aff_1)} = 
             {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        (is "?s1 = ?s2")
      proof(intro equalityI,standard)
        fix s
        assume "s \<in> ?s1"
        then have "s = proj_add (\<tau> (x1,y1),l1+1) ((x2, y2), l2)"
          using nt_in_class by auto
        then show "s \<in> ?s2"
          by blast
      next 
        show "?s2 \<subseteq> ?s1"
        proof(standard)
          fix s
          assume "s \<in> ?s2"
          then have "s = proj_add (\<tau> (x1, y1), l1 + 1) ((x2, y2), l2)"
            by auto
          then show "s \<in> ?s1"
            using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by blast     
        qed
      qed
       
      have "proj_add_class ?c1 ?c2 =
             {proj_add ((x1a, y1a), i) ((x2, y2), l2) |x1a y1a i. 
                 (((x1a,y1a),i) = ((x1,y1),l1) \<or> ((x1a,y1a),i) = (\<tau> (x1, y1),l1+1))
                 \<and> (((x1a, y1a), x2, y2) \<in> e_aff_0 \<or> ((x1a, y1a), x2, y2) \<in> e_aff_1)} // gluing"
        using aa assms by(simp del: \<tau>.simps)
      also have "... =  {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)} // gluing"
        using eq by auto
      finally have eq': "proj_add_class ?c1 ?c2 = {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)} // gluing" by auto
      then have "?c1 \<oplus> ?c2 = {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        unfolding proj_addition_def eq' 
        using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by blast
      have " gluing `` {proj_add' ((x1, y1), l1) ((x2, y2), l2)} =  {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by blast
      then show ?thesis
        using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by linarith
    next
      case bb (* symmetric *)
      have nz: "x2 \<noteq> 0" "y2 \<noteq> 0" "x1 = 0 \<or> y1 = 0"
        using assms(2) bb(2) e_proj_elim_2 in_aff(2) apply(fastforce,fastforce)
        using assms(1) bb(1) e_proj_elim_1 in_aff(1) by auto

      have "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
           "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0"
        subgoal
          using d(1) nz 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        subgoal
          using d(1) nz 
          unfolding delta_def delta_plus_def delta_minus_def 
                    delta'_def delta_x_def delta_y_def
          by fastforce
        done

      have eq: "{proj_add ((x1,y1),l1) ((x1a,y1a),i) |x1a y1a i. 
                 (((x1a,y1a),i) = ((x2,y2),l2) \<or> ((x1a,y1a),i) = (\<tau> (x2, y2),l2+1))
                 \<and> (((x1,y1), (x1a,y1a)) \<in> e_aff_0 \<or> ((x1,y1), (x1a,y1a)) \<in> e_aff_1)} = 
             {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)}"
        (is "?s1 = ?s2")
      proof(intro equalityI,standard)
        fix s
        assume "s \<in> ?s1"
        then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)"
          using nt_in_class by auto
        then show "s \<in> ?s2"
          by blast
      next 
        show "?s2 \<subseteq> ?s1"
        proof(standard)
          fix s
          assume "s \<in> ?s2"
          then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)"
            by auto
          then show "s \<in> ?s1"
            using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by blast      
        qed
      qed
       
      have "proj_add_class ?c1 ?c2 =
             {proj_add ((x1,y1),l1) ((x1a,y1a),i) |x1a y1a i. 
                 (((x1a,y1a),i) = ((x2,y2),l2) \<or> ((x1a,y1a),i) = (\<tau> (x2, y2),l2+1))
                 \<and> (((x1,y1), (x1a,y1a)) \<in> e_aff_0 \<or> ((x1,y1), (x1a,y1a)) \<in> e_aff_1)} // gluing"
        using bb assms by(simp del: \<tau>.simps)
      also have "... =  {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)} // gluing"
        using eq by auto
      finally have eq': "proj_add_class ?c1 ?c2 = {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)} // gluing" by auto
      then have "?c1 \<oplus> ?c2 = {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)}"
        unfolding proj_addition_def eq' 
        using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by blast
      have " gluing `` {proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)} =  {proj_add (\<tau> (x1,y1),l1+1) ((x2,y2),l2)}"
        using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by blast
      then show ?thesis
        using \<open>delta' x1 y1 (fst (\<tau> (x2, y2))) (snd (\<tau> (x2, y2))) = 0\<close> d(3) by linarith
    next
      case cc
       have nz: "x2 \<noteq> 0" "y2 \<noteq> 0" "x1 \<noteq> 0" "y1 \<noteq> 0"
         using cc assms e_proj_elim_1 e_proj_elim_2 in_aff by force+

      have "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0"
        using d(3) by linarith
      have "delta' (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) x2 y2 \<noteq> 0"
        by (metis \<tau>.simps assms(1) d(3) e_proj_aff fst_conv gluing_inv in_aff(2) nz(3) nz(4) snd_conv tau_idemp_point tau_tau_d')
      have rev: "proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1) = proj_add (\<tau> (x1, y1), l1+1) ((x2, y2), l2)"
      proof -
        have "l1 + (l2 + 1) = l1 + 1 + l2" by simp
        then show ?thesis
          by (metis \<open>delta' (fst (\<tau> (x1, y1))) (snd (\<tau> (x1, y1))) x2 y2 \<noteq> 0\<close> assms(1) assms(2) d(3) e_proj_aff gluing_inv inversion_invariance_2 
                   nz(1) nz(2) nz(3) nz(4) prod.collapse proj_add.simps(2) fst_conv snd_conv)
      qed

      have eq: "{proj_add ((x, y), i) ((x', y'), j) | 
              x y i x' y' j. 
              ((x, y), i) \<in> ?c1 \<and> 
              ((x', y'), j) \<in> ?c2 \<and> 
              ((x, y), (x', y')) \<in> e_aff_0 \<union> e_aff_1} = 
            {proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)}"
         (is "?s1 = ?s2")
      proof(intro equalityI;standard)
        fix s
        assume "s \<in> ?s1"
        then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1) \<or> 
                   s = proj_add (\<tau> (x1, y1), l1+1) ((x2, y2), l2)"
          apply(simp del: \<tau>.simps)
          using nt_in_class 
          by (metis gluing_char)
        then show "s \<in> ?s2"
          using rev by auto
      next 
        fix s
        assume "s \<in> ?s2"
        then have "s = proj_add ((x1,y1),l1) (\<tau> (x2,y2),l2+1)"
          by auto
        then show "s \<in> ?s1"
        proof -
          have "((x1,y1),\<tau> (x2,y2)) \<in> e_aff_1"
            unfolding e_aff_1_def apply(simp del: \<tau>.simps)
            by (metis (mono_tags, lifting) assms(2) d(3) e_proj_aff gluing_inv in_aff(1) nz(1) nz(2) prod.case_eq_if prod.collapse)
          have "(((x2, y2), l2), (\<tau> (x2, y2), l2+1)) \<in> gluing"
            using cc(2) by auto
          then show ?thesis
            apply(simp del: \<tau>.simps)
            using \<open>((x1, y1), \<tau> (x2, y2)) \<in> e_aff_1\<close> \<open>s = proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2 + 1)\<close> cc(1) by fastforce
        qed
      qed     
      
      have "proj_add_class ?c1 ?c2 =
             {proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)} // gluing"
        using assms eq by auto
      then have "?c1 \<oplus> ?c2 =
             \<langle>proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)\<rangle>"
      proof -
        have "proj_add_class ?c1 ?c2 \<noteq> {}"
          using assms(1) assms(2) covering by blast
        then have "?c1 \<oplus> ?c2 = \<langle>proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)\<rangle>"
          by (simp add: \<open>proj_add_class (gluing `` {((x1, y1), l1)}) (gluing `` {((x2, y2), l2)}) = {proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2 + 1)} // gluing\<close> proj_addition_def singleton_quotient)
        then show ?thesis by auto
      qed
      have "proj_add' ((x1, y1), l1) ((x2, y2), l2) = proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2+1)"
        using d by(simp del: \<tau>.simps)
      then show ?thesis 
        by (simp add: \<open>\<langle>((x1, y1), l1)\<rangle> \<oplus> \<langle>((x2, y2), l2)\<rangle> = \<langle>proj_add ((x1, y1), l1) (\<tau> (x2, y2), l2 + 1)\<rangle>\<close>)
    qed
  qed
qed

lemma independence_points:
  assumes "\<langle>(p,l1)\<rangle> \<in> e_proj" "\<langle>(q,l2)\<rangle> \<in> e_proj" 
  shows "\<langle>(p,l1)\<rangle> \<oplus> \<langle>(q,l2)\<rangle> = \<langle>proj_add' (p,l1) (q,l2)\<rangle>"
  using assms independence by(cases "p",cases "q",force)  

subsubsection \<open>Basic properties\<close>

theorem well_defined:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "p \<oplus> q \<in> e_proj"
proof -
  obtain x y l x' y' l'
    where p_q_expr: "p = \<langle>((x,y),l)\<rangle>"
                    "q = \<langle>((x',y'),l')\<rangle>"
    using e_proj_def assms
    apply(simp)
    apply(elim quotientE)
    by force
  then have in_aff: "(x,y) \<in> e_aff" 
                    "(x',y') \<in> e_aff" 
    using e_proj_aff assms by auto

  consider 
   (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (b) "((x, y), x', y') \<in> e_aff_0" 
         "((x, y), x', y') \<notin> e_aff_1" 
         "(x, y) \<notin> e_circ \<or> \<not> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (c) "((x, y), x', y') \<in> e_aff_1" 
    using dichotomy_1[OF in_aff] by auto
  then show ?thesis
  proof(cases)
    case a
    then obtain g where sym_expr: "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" by auto        
    then have ds: "delta x y x' y' = 0" "delta' x y x' y' = 0"
      using wd_d_nz wd_d'_nz a by auto
    have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
    proof -
      from a show "x \<noteq> 0" "y \<noteq> 0"
        unfolding e_circ_def by auto
      then show "x' \<noteq> 0" "y' \<noteq> 0" 
        using sym_expr t_nz
        unfolding symmetries_def e_circ_def 
        by auto
    qed
    have taus: "\<tau> (x',y') \<in> e_aff"
      using in_aff(2) e_circ_def nz(3,4) \<tau>_circ by force
    then have proj: "gluing `` {(\<tau> (x', y'), l'+1)} \<in> e_proj"
                    "\<langle>((x,y),l)\<rangle> \<in> e_proj"
      using e_proj_aff in_aff by auto

    have alt_ds: "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0 \<or>
                  delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
      (is "?d1 \<noteq> 0 \<or> ?d2 \<noteq> 0")
      using covering_with_deltas ds in_aff p_q_expr by blast

    have "proj_addition p q = proj_addition (\<langle>((x,y),l)\<rangle>) (\<langle>((x',y'),l')\<rangle>)"
      (is "?lhs = proj_addition ?p ?q")
      unfolding p_q_expr by simp
    also have "... = proj_addition ?p (gluing `` {(\<tau> (x', y'), l'+1)})"
      (is "_ = ?rhs")
      using gluing_inv nz in_aff by presburger
    finally have "?lhs = ?rhs"
      by auto
    then have eqs: 
      "?d1 \<noteq> 0 \<Longrightarrow> ?lhs = gluing `` {(add (x, y) (\<tau> (x', y')), l+l'+1)}"
      "?d2 \<noteq> 0 \<Longrightarrow> ?lhs = gluing `` {(ext_add (x, y) (\<tau> (x', y')), l+l'+1)}"
      using gluing_add gluing_ext_add proj alt_ds 
      by (metis (no_types, lifting) add.assoc prod.collapse)+
    have closures:
        "?d1 \<noteq> 0 \<Longrightarrow> add (x, y) (\<tau> (x', y')) \<in> e_aff"
        "?d2 \<noteq> 0 \<Longrightarrow> ext_add (x, y) (\<tau> (x', y')) \<in> e_aff"
      using e_proj_aff add_closure in_aff taus delta_def e_aff_def 
       apply fastforce
      using e_proj_aff ext_add_closure in_aff taus delta_def e_aff_def 
       by fastforce
      
    have f_proj: "?d1 \<noteq> 0 \<Longrightarrow> gluing `` {(add (x, y) (\<tau> (x', y')), l+l'+1)} \<in> e_proj"
                 "?d2 \<noteq> 0 \<Longrightarrow> gluing `` {(ext_add (x, y) (\<tau> (x', y')), l+l'+1)} \<in> e_proj"
      using e_proj_aff closures by force+
      
    then show ?thesis
      using eqs alt_ds by auto
  next
    case b
    then have ds: "delta x y x' y' \<noteq> 0"
      unfolding e_aff_0_def by auto

    have eq: "proj_addition p q = gluing `` {(add (x, y) (x',y'), l+l')}" 
      (is "?lhs = ?rhs")
      unfolding p_q_expr
      using gluing_add assms p_q_expr ds by meson
    have add_in: "add (x, y) (x',y') \<in> e_aff"
        using add_closure in_aff ds
        unfolding delta_def e_aff_def by auto
    then show ?thesis
      using eq e_proj_aff by auto  
  next
    case c
    then have ds: "delta' x y x' y' \<noteq> 0"
      unfolding e_aff_1_def by auto

    have eq: "proj_addition p q = gluing `` {(ext_add (x, y) (x',y'), l+l')}" 
      (is "?lhs = ?rhs")
      unfolding p_q_expr
      using gluing_ext_add assms p_q_expr ds by meson
    have add_in: "ext_add (x, y) (x',y') \<in> e_aff"
        using ext_add_closure in_aff ds
        unfolding delta_def e_aff_def by auto
    then show ?thesis
      using eq e_proj_aff by auto  
  qed
qed

lemma proj_add_class_inv:
  assumes "\<langle>(p,l)\<rangle>  \<in> e_proj"
  shows "\<langle>(p,l)\<rangle> \<oplus> \<langle>(i p,l')\<rangle> = {((1, 0), l+l')}"
        "\<langle>(i p,l')\<rangle> \<in> e_proj"  
proof -
  obtain x y where p_eq: "p = (x,y)"
    by fastforce
  have in_aff: "(x,y) \<in> e_aff" 
    using assms e_proj_aff p_eq by blast
  then have i_aff: "i (x, y) \<in> e_aff"
    using i_aff by blast
  show i_proj: "gluing `` {(i p,l')} \<in> e_proj"
    using e_proj_aff i_aff p_eq by simp

  consider (1) "delta x y x (-y) \<noteq> 0" | (2) "delta' x y x (-y) \<noteq> 0"
    using add_self in_aff by blast
  then show "proj_addition (\<langle>(p,l)\<rangle>) (gluing `` {(i p,l')}) = {((1, 0), l+l')}"
  proof(cases)
    case 1
    have "add (x,y) (i (x,y)) = (1,0)"
      using "1" delta_def delta_minus_def delta_plus_def in_aff inverse_generalized by auto
    then show ?thesis 
      using "1" assms gluing_add i_proj identity_equiv p_eq by auto
  next
    case 2
    have "ext_add p (i p) = (1,0)"
      using "2" delta'_def delta_x_def p_eq by auto
    then show ?thesis 
      using "2" assms gluing_ext_add i_proj identity_equiv p_eq by auto
  qed
qed

lemma proj_add_class_identity:
  assumes "x \<in> e_proj"
  shows "proj_addition {((1, 0), 0)} x = x"
proof -
  obtain x0 y0 l0 where 
    x_expr: "x = gluing `` {((x0,y0),l0)}"
    using assms e_proj_def
    apply(simp)
    apply(elim quotientE) 
    by force
  then have in_aff: "(x0,y0) \<in> e_aff"
    using e_proj_aff assms by blast

  have "({((1, 0), 0)} \<oplus> x) = (\<langle>((1, 0), 0)\<rangle> \<oplus> (gluing `` {((x0,y0),l0)}))"
    using identity_equiv[of 0] x_expr by argo
  also have "... = gluing `` {(add (1,0) (x0,y0),l0)}"
    apply(subst gluing_add)
    using identity_equiv identity_proj apply simp
    using x_expr assms apply simp
    unfolding delta_def delta_plus_def delta_minus_def apply simp
    by simp
  also have "... = gluing `` {((x0,y0),l0)}"
    using inverse_generalized in_aff 
    unfolding e_aff_def by simp
  also have "... = x" 
    using x_expr by simp
  finally show ?thesis by simp
qed

corollary proj_addition_comm:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj" 
  shows "c1 \<oplus> c2 = (c2 \<oplus> c1)"
  using proj_add_class_comm[OF assms]
  unfolding proj_addition_def by auto

lemma proj_add'_aff:
  assumes "p \<in> e_aff" "q \<in> e_aff"
  shows "fst (proj_add' (p,l) (q,l')) \<in> e_aff"
proof- 
  consider 
    (1) "delta (fst p) (snd p) (fst q) (snd q) \<noteq> 0 \<or> 
         delta' (fst p) (snd p) (fst q) (snd q) \<noteq> 0" |
    (2) "delta (fst p) (snd p) (fst q) (snd q) = 0" 
        "delta' (fst p) (snd p) (fst q) (snd q) = 0" 
        "delta (fst p) (snd p) (fst (\<tau> q)) (snd (\<tau> q)) \<noteq> 0 \<or> 
        delta' (fst p) (snd p) (fst (\<tau> q)) (snd (\<tau> q)) \<noteq> 0" 
    using covering_with_deltas assms by(cases "p",cases "q",auto)  
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis 
      apply(cases "p", cases "q",safe)
      using add_closure ext_add_closure assms by auto
  next
    case 2
    have "fst q \<noteq> 0" "snd q \<noteq> 0" 
      using 2 
      unfolding delta_def delta_minus_def delta_plus_def 
      by force+
    then have in_aff: "\<tau> q \<in> e_aff"
      using \<tau>_circ e_circ_def assms(2) circ_to_aff by blast
    show ?thesis
      apply(cases "p",cases "q")
      using 2(3) apply(elim disjE)
      using add_closure[of "fst p" "snd p" "fst (\<tau> q)" "snd (\<tau> q)"]
            ext_add_closure[of "fst p" "snd p" "fst (\<tau> q)" "snd (\<tau> q)"]
            "2" in_aff assms by auto
  qed
qed

section \<open>Group law\<close>

subsection \<open>Class invariance on group operations\<close>

subsubsection \<open>tf\<close>

definition tf  where
  "tf g = image (\<lambda> p. (g (fst p), snd p))"

lemma tf_comp:
  "tf g (tf f s) = tf (g \<circ> f) s"
  unfolding tf_def by force

lemma tf_id:
  "tf id s = s"
  unfolding tf_def by fastforce

lemma remove_rho:
  assumes "\<langle>((x,y),l)\<rangle> \<in> e_proj"
  shows "tf \<rho> (\<langle>((x,y),l)\<rangle>) = \<langle>(\<rho> (x,y),l)\<rangle>"
proof -
  have in_aff: "(x,y) \<in> e_aff" 
      using assms e_proj_aff by blast
  have rho_aff: "\<rho> (x,y) \<in> e_aff" 
      using rot_aff[of \<rho>,OF _ in_aff] rotations_def by blast
  
  have eq: "\<langle>((x,y),l)\<rangle> = {((x, y), l)} \<or> 
            \<langle>((x,y),l)\<rangle> = {((x, y), l), (\<tau> (x, y), l+1)}"
    using assms gluing_cases_explicit by auto
  from eq consider  
    (1) "\<langle>((x,y),l)\<rangle> = {((x, y), l)}" | 
    (2) "\<langle>((x,y),l)\<rangle> = {((x, y), l), (\<tau> (x, y), l+1)}"
    by fast
  then show "tf \<rho> (\<langle>((x,y),l)\<rangle>) = \<langle>(\<rho> (x,y),l)\<rangle>"
  proof(cases)
    case 1
    have zeros: "x = 0 \<or> y = 0"
      using in_aff e_proj_elim_1 assms e_proj_aff 1 by auto
    then have "\<langle>(\<rho> (x,y),l)\<rangle> = {(\<rho> (x, y), l)}"
      using gluing_class_1[of "\<rho> (x, y)" l,OF _ rho_aff] by fastforce 
    then show ?thesis 
      unfolding tf_def image_def 1 by simp
  next
    case 2
    have zeros: "x \<noteq> 0" "y \<noteq> 0"
      using in_aff e_proj_elim_2 assms e_proj_aff 2 by fastforce+
    then have "\<langle>(\<rho> (x,y),l)\<rangle> = {(\<rho> (x, y), l), (\<tau> (\<rho> (x, y)), l+1)}"
      using gluing_class_2[of "(\<rho> (x, y))", OF _ _ rho_aff] by force   
    then show ?thesis 
      unfolding tf_def image_def 2 by force
  qed
qed

lemma rho_preserv_e_proj:
  assumes "\<langle>(p,l)\<rangle> \<in> e_proj"
  shows "tf \<rho> (\<langle>(p,l)\<rangle>) \<in> e_proj"
proof -
  obtain x y where p_eq: "p = (x,y)"
    by fastforce
  have in_aff: "(x,y) \<in> e_aff" 
      using assms e_proj_aff p_eq by blast
  have rho_aff: "\<rho> (x,y) \<in> e_aff" 
      using rot_aff[of \<rho>,OF _ in_aff] rotations_def by blast
  show ?thesis
    using assms e_proj_aff p_eq remove_rho rho_aff by auto
qed

lemma remove_rotations:
  assumes "\<langle>((x,y),l)\<rangle> \<in> e_proj" "r \<in> rotations"
  shows "tf r (\<langle>((x,y),l)\<rangle>) = \<langle>(r (x,y),l)\<rangle>"
proof -
  have in_proj: "\<langle>(\<rho> (x,y),l)\<rangle> \<in> e_proj" "gluing `` {((\<rho> \<circ> \<rho>) (x, y), l)} \<in> e_proj"
      using rho_preserv_e_proj assms remove_rho by auto+

  consider (1) "r = id" | (2) "r = \<rho>" | (3) "r = \<rho> \<circ> \<rho>" | (4) "r = \<rho> \<circ> \<rho> \<circ> \<rho>" 
    using assms(2) unfolding rotations_def by fast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using tf_id by auto
  next
    case 2
    then show ?thesis using remove_rho assms by presburger 
  next
    case 3    
    then show ?thesis 
      using remove_rho assms tf_comp in_proj(1) 
      by (metis (no_types, lifting) \<rho>.simps comp_apply)
  next
    case 4
    then show ?thesis 
      using remove_rho assms tf_comp in_proj 
      by (metis (no_types, lifting) \<rho>.simps comp_apply)
  qed
qed

lemma rotation_preserv_e_proj:
  assumes "\<langle>((x,y),l)\<rangle> \<in> e_proj" "r \<in> rotations"
  shows "tf r (\<langle>((x,y),l)\<rangle>) \<in> e_proj"
  (is "tf ?r ?g \<in> _")
  using assms
  unfolding rotations_def
  apply(safe)
  using tf_id[of ?g] apply simp
  using rho_preserv_e_proj apply simp
  using tf_comp rho_preserv_e_proj remove_rho 
  by(metis (no_types, hide_lams) prod.collapse)+

lemma tf_proj_add':
  assumes "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"
  shows "proj_add' (\<rho> (x,y),l) ((x',y'),l') = (\<lambda> p. (\<rho> (fst p), snd p)) (proj_add' ((x,y),l) ((x',y'),l'))"
proof(cases "delta x y x' y' \<noteq> 0 \<or> delta' x y x' y' \<noteq> 0")
  case True
  then show ?thesis
    apply(elim disjE)
    using assms delta_com e_proj_aff remove_rho rho_invariance_1 
          rho_preserv_e_proj rotation_invariance_3 
    apply force
    using assms delta'_com e_proj_aff remove_rho rho_invariance_2 
          rho_preserv_e_proj rotation_invariance_4 
    by auto
next
  case False
  have nz: "x' \<noteq> 0" "y' \<noteq> 0"
      using False
      unfolding delta_def delta_minus_def delta_plus_def 
                delta'_def delta_x_def delta_y_def 
      by force+
  have in_aff: "\<rho> (x,y) \<in> e_aff" "\<tau> (x',y') \<in> e_aff"
      using assms(1) rot_aff rotations_def apply blast
      using nz \<tau>_circ e_circ_def assms(2) by auto
  consider (1) "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0" | 
           (2) "delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0" 
    using covering_with_deltas e_proj_aff False assms by blast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis
    proof -
      from 1 have eq1: "proj_add' (\<rho> (x, y), l) ((x', y'), l') = proj_add (\<rho> (x, y), l) (\<tau> (x', y'), l'+1)"
                       "proj_add' ((x, y), l) ((x', y'), l') = proj_add ((x, y), l) (\<tau> (x', y'), l'+1)"
        using False delta'_com delta_com rotation_invariance_3 rotation_invariance_4 by auto
      then have "proj_add (\<rho> (x, y), l) (\<tau> (x', y'), l'+1) = (add (\<rho> (x,y)) (\<tau> (x',y')), l+l'+1)"
      proof -
        have "delta (fst (\<rho> (x,y))) (snd (\<rho> (x,y))) (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
          by (metis "1" delta_com rotation_invariance_3)
        then show ?thesis
          using in_aff by simp
      qed
      have eq3: "\<rho> (fst (proj_add ((x, y), l) (\<tau> (x', y'), l' + 1))) = add (\<rho> (x,y)) (\<tau> (x',y'))"
        by (metis "1" assms(1) fst_conv in_aff(2) prod.collapse proj_add.simps(1) rho_invariance_1)
      then show ?thesis
        using "1" \<open>proj_add (\<rho> (x, y), l) (\<tau> (x', y'), l' + 1) = (add (\<rho> (x, y)) (\<tau> (x', y')), l + l' + 1)\<close> assms(1) eq1(1) eq1(2) in_aff(2) by auto
    qed
  next
    case 2
    then show ?thesis 
    proof -
      from 2 have eq1: "proj_add' (\<rho> (x, y), l) ((x', y'), l') = proj_add (\<rho> (x, y), l) (\<tau> (x', y'), l'+1)"
                       "proj_add' ((x, y), l) ((x', y'), l') = proj_add ((x, y), l) (\<tau> (x', y'), l'+1)"
        using False delta'_com delta_com rotation_invariance_3 rotation_invariance_4 by auto
      then have "proj_add (\<rho> (x, y), l) (\<tau> (x', y'), l'+1) = (ext_add (\<rho> (x,y)) (\<tau> (x',y')), l+l'+1)"
      proof -
        have "delta' (fst (\<rho> (x,y))) (snd (\<rho> (x,y))) (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
          by (metis "2" add.inverse_inverse add.inverse_neutral delta'_com rotation_invariance_4)
        then show ?thesis
          using in_aff by simp
      qed
      have eq3: "\<rho> (fst (proj_add ((x, y), l) (\<tau> (x', y'), l' + 1))) = ext_add (\<rho> (x,y)) (\<tau> (x',y'))"
        by (metis "2" assms(1) fst_conv in_aff(2) prod.collapse proj_add.simps(2) rho_invariance_2)
      then show ?thesis
        using "2" \<open>proj_add (\<rho> (x, y), l) (\<tau> (x', y'), l' + 1) = (ext_add (\<rho> (x, y)) (\<tau> (x', y')), l + l' + 1)\<close> assms(1) eq1 in_aff(2) by auto
    qed
  qed
qed

lemma tf_proj_add'_rot:
  assumes "p \<in> e_aff" "q \<in> e_aff" "r \<in> rotations"
  shows "proj_add' (r p,l) (q,l') = (\<lambda> p. (r (fst p), snd p)) (proj_add' (p,l) (q,l'))"
  apply(cases "p",cases "q")
  using assms(3) unfolding rotations_def
  apply(simp del: \<tau>.simps proj_add'.simps,elim disjE)
  apply simp
  using tf_proj_add' assms apply simp
   apply(simp_all add: tf_proj_add' del: \<rho>.simps \<tau>.simps proj_add'.simps)
  by(metis \<rho>.simps assms(1) assms(2) fst_conv insertCI rot_aff rotations_def snd_conv tf_proj_add')+

lemma remove_add_rho:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "(tf \<rho> p) \<oplus> q = tf \<rho> (p \<oplus> q)"
proof -
  obtain x y l x' y' l' where 
    p_q_expr: "p = \<langle>((x,y),l)\<rangle>" 
              "q = \<langle>((x',y'),l')\<rangle>"
    using assms
    unfolding e_proj_def
    apply(elim quotientE)
    by force
  have e_proj:
    "\<langle>((x,y),l)\<rangle> \<in> e_proj" 
    "\<langle>((x',y'),l')\<rangle> \<in> e_proj"
    using p_q_expr assms by auto
  then have rho_e_proj: 
    "\<langle>(\<rho> (x,y),l)\<rangle> \<in> e_proj"
    using remove_rho rho_preserv_e_proj by auto

  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    using assms p_q_expr e_proj_aff by auto

  have "(tf \<rho> p \<oplus> q) = (\<langle>(\<rho> (x,y),l)\<rangle> \<oplus> q)"
    using assms(1) p_q_expr(1) remove_rho by auto
  also have "... = (\<langle>proj_add' (\<rho> (x,y),l) ((x',y'),l')\<rangle>)"
    using e_proj(2) independence p_q_expr(2) rho_e_proj by auto
  also have "... = \<langle>(\<lambda> p. (\<rho> (fst p), snd p)) (proj_add' ((x,y),l) ((x',y'),l'))\<rangle>"
    using in_aff(1) in_aff(2) tf_proj_add' by auto
  also have "... = tf \<rho> (p \<oplus> q)"
    by (metis assms(1) assms(2) independence p_q_expr(1) p_q_expr(2) remove_rho surjective_pairing well_defined)
  finally show ?thesis
    by auto
qed

lemma remove_add_rotation:
  assumes "p \<in> e_proj" "q \<in> e_proj" "r \<in> rotations"
  shows "proj_addition (tf r p) q = tf r (proj_addition p q)"
proof -
  obtain x y l x' y' l' where p_q_expr: "p = \<langle>((x,y),l)\<rangle>" "p = \<langle>((x',y'),l')\<rangle>"
    by (metis assms(1) e_proj_def prod.collapse quotientE)
  consider (1) "r = id" | (2) "r = \<rho>" | (3) "r = \<rho> \<circ> \<rho>" | (4) "r = \<rho> \<circ> \<rho> \<circ> \<rho>" 
    using assms(3) unfolding rotations_def by fast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using tf_id by metis
  next
    case 2
    then show ?thesis using remove_add_rho assms(1,2) by auto
  next
    case 3        
    then show ?thesis 
      unfolding p_q_expr
      using remove_add_rho assms(1,2)  rho_preserv_e_proj remove_rho 
      by (metis (no_types, lifting) p_q_expr(1) tf_comp)
  next
    case 4
    then show ?thesis 
      unfolding p_q_expr
      using remove_add_rho assms(1,2) rho_preserv_e_proj remove_rho 
      by (smt \<rho>.simps p_q_expr(1) p_q_expr(2) tf_comp)
  qed
qed

subsubsection \<open>tf'\<close>

definition tf' where
  "tf' = image (\<lambda> p. (fst p, (snd p)+1))"

lemma tf_tau:
  assumes "\<langle>(p,l)\<rangle> \<in> e_proj" 
  shows "tf' (\<langle>(p,l)\<rangle>) = \<langle>(p,l+1)\<rangle>"
  using assms unfolding symmetries_def
proof -
  have in_aff: "p \<in> e_aff" 
    using e_proj_aff assms by simp

  have gl_expr: "\<langle>(p,l)\<rangle> = {(p,l)} \<or> 
                 \<langle>(p,l)\<rangle> = {(p,l),(\<tau> p,l+1)}"
    using assms gluing_cases_explicit by(cases "p",simp)

  consider (1) "\<langle>(p,l)\<rangle> = {(p,l)}" | 
           (2) "\<langle>(p,l)\<rangle> = {(p,l),(\<tau> p,l+1)}" 
    using gl_expr by argo
  then show "tf' (gluing `` {(p, l)}) = gluing `` {(p, l+1)}"
  proof(cases)
    case 1   
    then have zeros: "fst p = 0 \<or> snd p = 0"
      using e_proj_elim_1 in_aff assms by auto
    show ?thesis 
      apply(simp add: 1 tf'_def del: \<tau>.simps)
      using gluing_class_1 zeros in_aff by auto
  next
    case 2
    then have zeros: "fst p \<noteq> 0" "snd p \<noteq> 0" 
      using assms e_proj_elim_2 in_aff by fastforce+
    show ?thesis 
      apply(simp add: 2 tf'_def del: \<tau>.simps)
      using gluing_class_2 zeros in_aff by auto
  qed
qed

lemma tf_preserv_e_proj:
  assumes "\<langle>(p,l)\<rangle> \<in> e_proj" 
  shows "tf' (\<langle>(p,l)\<rangle>) \<in> e_proj"
  using assms tf_tau[OF assms] 
        e_proj_aff[of "p" l] e_proj_aff[of "p" "l+1"] by(cases "p",simp) 

lemma remove_tau:
  assumes "\<langle>(p,l)\<rangle> \<in> e_proj" "\<langle>(\<tau> p,l)\<rangle> \<in> e_proj"
  shows "tf' (\<langle>(p,l)\<rangle>) = \<langle>(\<tau> p,l)\<rangle>"
  (is "tf' ?g = ?gt")
proof -
  have in_aff: "p \<in> e_aff" "\<tau> p \<in> e_aff" 
    using assms e_proj_aff by simp+

  consider (1) "?gt = {(\<tau> p,l)}" | (2) "?gt = {(\<tau> p,l),(p,l+1)}"
    using tau_idemp_point gluing_cases_points[OF assms(2), of "\<tau> p" l] by presburger 
  then show ?thesis
  proof(cases)
    case 1
    then have zeros: "fst p = 0 \<or> snd p = 0"
      using e_proj_elim_1 in_aff assms by(cases "p",simp add: t_nz) 
    have "False"
      using zeros in_aff t_n1 d_n1 
      unfolding e_aff_def e_def 
      apply(cases "p",simp)
      by(simp_all split: if_splits add: t_sq_n1 d_n1 divide_simps t_nz power_mult_distrib[of t _ 2])

    then show ?thesis by simp
  next
    case 2
    then have zeros: "fst p \<noteq> 0" "snd p \<noteq> 0"
      using e_proj_elim_2[OF in_aff(2), of l, simplified tau_idemp_point] 
            in_aff assms gluing_class_1 by(cases "p",force)+  
    then have gl_eq: "\<langle>(p,l)\<rangle> = {(p,l),(\<tau> p,l+1)}"
      using in_aff gluing_class_2 by auto
    then show ?thesis 
      by(simp add: 2 gl_eq tf'_def del: \<tau>.simps,fast) 
  qed
qed

lemma tf_tf'_commute:
  "tf r (tf' p) = tf' (tf r p)"
  unfolding tf'_def tf_def image_def
  by auto

lemma tf'_proj_add':
  assumes "(x,y) \<in> e_aff" "(x',y') \<in> e_aff"
  shows "proj_add' ((x,y),l+1) ((x',y'),l') = (\<lambda> p. (fst p, snd p+1)) (proj_add' ((x,y),l) ((x',y'),l'))"
proof(cases "delta x y x' y' \<noteq> 0 \<or> delta' x y x' y' \<noteq> 0")
  case True
  then show ?thesis
    using assms(1) assms(2) by auto
next
  case False
  have nz: "x' \<noteq> 0" "y' \<noteq> 0"
      using False
      unfolding delta_def delta_minus_def delta_plus_def 
                delta'_def delta_x_def delta_y_def 
      by force+
  have in_aff: "\<tau> (x',y') \<in> e_aff"
      using nz \<tau>_circ e_circ_def assms(2) by auto
  from False have "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0 \<or>
                  delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
    using assms(1) assms(2) covering_with_deltas e_proj_aff by blast
  then show ?thesis
    using False assms(1) in_aff by auto
qed

lemma remove_add_tau:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "(tf' p) \<oplus> q = tf' (p \<oplus> q)"
proof -
  obtain x y l x' y' l' where 
    p_q_expr: "p = \<langle>((x,y),l)\<rangle>" 
              "q = \<langle>((x',y'),l')\<rangle>"
    using assms
    unfolding e_proj_def
    apply(elim quotientE)
    by force
  have e_proj:
    "\<langle>((x,y),s)\<rangle> \<in> e_proj" 
    "\<langle>((x',y'),s')\<rangle> \<in> e_proj" for s s'
    using p_q_expr assms e_proj_aff by auto
  have in_aff: "(x,y) \<in> e_aff" "(x',y') \<in> e_aff" 
    using assms p_q_expr e_proj_aff by auto

  have other_proj:
    "\<langle>((x,y),l+1)\<rangle> \<in> e_proj" 
    using in_aff e_proj_aff by auto

  have "(tf' p) \<oplus> q = (\<langle>((x,y),l+1)\<rangle> \<oplus> q)"
    using assms(1) p_q_expr(1) tf_tau by auto
  also have "... = \<langle>proj_add' ((x,y),l+1) ((x',y'),l')\<rangle>"
    using assms(2) independence other_proj p_q_expr(2) by auto
  also have "... = \<langle>(\<lambda> p. (fst p, snd p+1)) (proj_add' ((x,y),l) ((x',y'),l'))\<rangle>"
    using tf'_proj_add'[OF in_aff,of l l'] by argo
  also have "... = tf' (p \<oplus> q)"
    by (metis e_proj(1) e_proj(2) ext_curve_addition.independence ext_curve_addition_axioms 
              p_q_expr(1) p_q_expr(2) surjective_pairing tf_tau well_defined)
  finally show ?thesis
    by auto
qed

lemma remove_add_tau':
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "proj_addition p (tf' q) = tf' (proj_addition p q)"
  using assms proj_addition_comm remove_add_tau 
  by (metis proj_add_class.simps(2) proj_addition_def)

lemma tf'_idemp:
  assumes "s \<in> e_proj"
  shows "tf' (tf' s) = s"
proof -
  obtain x y l where p_q_expr: 
    "s = \<langle>((x,y),l)\<rangle>"
    by (metis assms e_proj_def prod.collapse quotientE)
  then have "s = {((x, y), l)} \<or> s = {((x, y), l), (\<tau> (x, y), l+1)}"  
    using assms gluing_cases_explicit by auto
  then show ?thesis 
    apply(elim disjE)
    by(simp add: tf'_def)+
qed

lemma tf'_injective:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj"
  assumes "tf' (c1) = tf' (c2)"
  shows "c1 = c2"
  using assms by (metis tf'_idemp)

subsubsection \<open>tf''\<close>

definition tf'' where
 "tf'' g s = tf' (tf g s)"

lemma remove_add_rot:
  assumes "p \<in> e_proj" "q \<in> e_proj" "g \<in> rotations"
  shows "(tf'' g p) \<oplus> q = tf'' g (p \<oplus> q)"
proof -
  obtain x y l x' y' l' where p_q_expr: "p =  \<langle>((x,y),l)\<rangle>" "q =  \<langle>((x',y'),l')\<rangle>"
    by (metis assms(1,2) e_proj_def prod.collapse quotientE)+
  then have e_proj: "(tf g p) \<in> e_proj"
    using rotation_preserv_e_proj assms by fast  
  have "proj_addition (tf'' g p) q = proj_addition (tf' (tf g p)) q"
    unfolding tf''_def by simp
  also have "... = tf' (proj_addition (tf g p) q)"
    using remove_add_tau assms e_proj by blast
  also have "... = tf' (tf g (proj_addition p q))"
    using remove_add_rotation assms by presburger
  also have "... = tf'' g (proj_addition p q)"
    using tf''_def by auto
  finally show ?thesis by simp
qed

lemma tf''_preserv_e_proj:
  assumes "p \<in> e_proj" "r \<in> rotations"
  shows "tf'' r p \<in> e_proj"
proof -
  obtain x y l where p_eq: "p = \<langle>((x,y),l)\<rangle>"  
    using assms(1) unfolding e_proj_def
    by(elim quotientE,force) 
  then have p_hyp: "\<langle>((x,y),l)\<rangle> \<in> e_proj" "r \<in> rotations"
    using assms by auto
  show ?thesis
    unfolding tf''_def
    apply(rewrite p_eq)
    apply(subst remove_rotations[OF p_hyp])
    using rotation_preserv_e_proj[OF p_hyp] tf_preserv_e_proj remove_rotations[OF p_hyp] 
    by simp
qed

lemma remove_add_rot_comm:
  assumes "p \<in> e_proj" "q \<in> e_proj" "g \<in> rotations"
  shows "p \<oplus> (tf'' g q) = tf'' g (p \<oplus> q)"
proof -
  have "p \<oplus> (tf'' g q) = ((tf'' g q) \<oplus> p)" 
    using proj_addition_comm[OF tf''_preserv_e_proj[OF assms(2,3)] assms(1)] by auto
  also have "... = tf'' g (q \<oplus> p)"
    using remove_add_rot[OF assms(2,1,3)] by auto
  also have "... = tf'' g (p \<oplus> q)"
    using proj_addition_comm[OF assms(1,2)] by auto
  finally show ?thesis
    by auto
qed

lemma remove_sym:
  assumes "\<langle>((x,y),l)\<rangle> \<in> e_proj" "\<langle>(g (x, y), l)\<rangle> \<in> e_proj" "g \<in> symmetries"
  shows "\<langle>(g (x, y), l)\<rangle> = tf'' (\<tau> \<circ> g) (\<langle>((x,y),l)\<rangle>)"
proof -
  obtain r where r_expr: "r \<in> rotations" "g = \<tau> \<circ> r"
    using assms sym_decomp by blast
  then have e_proj: "\<langle>(r (x,y),l)\<rangle> \<in> e_proj"
    using rotation_preserv_e_proj remove_rotations assms by simp
  have "gluing `` {(g (x, y), l)} = gluing `` {(\<tau> (r (x, y)), l)}"
    using r_expr by simp
  also have "... = tf' (\<langle>(r (x,y),l)\<rangle>)"
    using remove_tau assms e_proj r_expr by simp
  also have "... = tf' (tf r (\<langle>((x,y),l)\<rangle>))"
    using remove_rotations r_expr assms(1) by force
  also have "... = tf'' (\<tau> \<circ> g) (\<langle>((x,y),l)\<rangle>)"
    using r_expr(2) tf''_def tau_idemp_explicit 
    by (metis (no_types, lifting) comp_assoc id_comp tau_idemp)
  finally show ?thesis by simp
qed  

lemma get_sym:
  assumes "\<langle>(p,l)\<rangle> \<in> e_proj" "\<langle>((\<tau> \<circ> g) p, l)\<rangle> \<in> e_proj" "g \<in> rotations"
  shows "\<langle>((\<tau> \<circ> g) p, l)\<rangle> = tf'' g (\<langle>(p,l)\<rangle>)"
proof -
  obtain x y where p_eq: "p = (x,y)" using assms by fastforce
  have "\<tau> \<circ> g \<in> symmetries"
    using assms(3) tau_rot_sym by blast
  then have "\<langle>((\<tau> \<circ> g) (x, y), l)\<rangle> = tf'' (\<tau> \<circ> (\<tau> \<circ> g)) (\<langle>((x,y),l)\<rangle>)"
    using remove_sym assms p_eq by auto
  also have "... = tf'' g (\<langle>((x,y),l)\<rangle>)"
    by (simp add: o_assoc tau_idemp)
  finally show ?thesis
    using p_eq by auto
qed  

subsection \<open>Associativities\<close>

lemma fstI: "x = (y, z) \<Longrightarrow> y = fst x" by simp

lemma sndI: "x = (y, z) \<Longrightarrow> z = snd x" by simp

ML \<open>
fun basic_equalities assms ctxt z1' z3' =
let 
  (* Basic equalities *)
  
  val th1 = @{thm fstI}  OF  [(nth assms 0)]
  val th2 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "fst::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 2)])
  val x1'_expr = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop 
                             (HOLogic.mk_eq (@{term "x1'::'a"},HOLogic.mk_fst z1')))
                            (fn _ =>
                                    EqSubst.eqsubst_tac ctxt [1] [th1] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th2] 1
                                    THEN simp_tac ctxt 1)
  val th3 = @{thm sndI}  OF  [(nth assms 0)]
  val th4 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "snd::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 2)])
  val y1'_expr = Goal.prove ctxt [] []
                                 (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "y1'::'a"},HOLogic.mk_snd z1')))
                            (fn _ => EqSubst.eqsubst_tac ctxt [1] [th3] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th4] 1
                                    THEN simp_tac ctxt 1)

  val th5 = @{thm fstI}  OF  [(nth assms 1)]
  val th6 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "fst::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 3)])
  val x3'_expr = Goal.prove ctxt [] []
                                 (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "x3'::'a"},HOLogic.mk_fst z3')))
                            (fn _ => EqSubst.eqsubst_tac ctxt [1] [th5] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th6] 1
                                    THEN simp_tac ctxt 1)
  
  val th7 = @{thm sndI}  OF  [(nth assms 1)]
  val th8 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "snd::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 3)])
  val y3'_expr = Goal.prove ctxt [] []
                                 (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "y3'::'a"},HOLogic.mk_snd z3')))
                            (fn _ => EqSubst.eqsubst_tac ctxt [1] [th7] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th8] 1
                                    THEN simp_tac ctxt 1)
in 
  (x1'_expr,y1'_expr,x3'_expr,y3'_expr)
end

fun rewrite_procedures ctxt =
let
  val rewrite1 =
    let 
      val pat = [Rewrite.In,Rewrite.Term 
                  (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),
                Rewrite.At]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric]}) 1 
     end
  
  val rewrite2 =
    let 
      val pat = [Rewrite.In,Rewrite.Term 
                  (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),
                 Rewrite.In]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric] 
                               }) 1 
     end;

  val rewrite3 =
     let 
      val pat = [Rewrite.In,Rewrite.Term (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ 
                                          Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),Rewrite.At]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric]}) 1 
     end
  
  val rewrite4 =
    let 
      val pat = [Rewrite.In,Rewrite.Term (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ 
                                         Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),Rewrite.In]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric]}) 1 
     end 
in 
  (rewrite1,rewrite2,rewrite3,rewrite4)
end


fun concrete_assoc first second third fourth =
let
 
  val ctxt0 = @{context};
  val ctxt = ctxt0;
  val (_,ctxt) = Variable.add_fixes ["z1'","x1'","y1'",
                                     "z3'","x3'", "y3'", 
                                     "x1", "y1", "x2", "y2", "x3", "y3"] ctxt

  val z1' = if first = "ext" then @{term "ext_add (x1,y1) (x2,y2)"} else @{term "add (x1,y1) (x2,y2)"}
  val z3' = if fourth = "ext" then @{term "ext_add (x2,y2) (x3,y3)"} else @{term "add (x2,y2) (x3,y3)"}
  val lhs = if second = "ext" then (fn z1' => @{term "ext_add"} $ z1' $ @{term "(x3::'a,y3::'a)"}) 
                              else (fn z1' => @{term "add"} $ z1' $ @{term "(x3::'a,y3::'a)"})
  val rhs = if third = "ext" then (fn z3' => @{term "ext_add (x1,y1)"} $ z3')
                             else (fn z3' => @{term "add (x1,y1)"} $ z3') 

  val delta1 = case z1' of @{term "ext_add"} $ _ $ _ => [@{term "delta' x1 y1 x2 y2"},@{term "delta_x x1 y1 x2 y2"},@{term "delta_y x1 y1 x2 y2"}]
                         | @{term "add"} $ _ $ _     => [@{term "delta x1 y1 x2 y2"},@{term "delta_minus x1 y1 x2 y2"},@{term "delta_plus x1 y1 x2 y2"}]
                         | _ => [] (* fix, raise some appropriate exception *)
  val delta2 = case (lhs @{term "z1'::'a \<times> 'a"}) of 
                           @{term "ext_add"} $ _ $ _ => [@{term "delta_x x1' y1' x3 y3"},@{term "delta_y x1' y1' x3 y3"}]
                         | @{term "add"} $ _ $ _     => [@{term "delta_minus x1' y1' x3 y3"},@{term "delta_plus x1' y1' x3 y3"}]
                         | _ => [] (* fix, raise some appropriate exception *)
  val delta3 = if third = "ext" then [@{term "delta_x x1 y1 x3' y3'"},@{term "delta_y x1 y1 x3' y3'"}]
                                else [@{term "delta_minus x1 y1 x3' y3'"},@{term "delta_plus x1 y1 x3' y3'"}]

  val delta4 = if fourth = "ext" then [@{term "delta' x2 y2 x3 y3"},@{term "delta_x x2 y2 x3 y3"},@{term "delta_y x2 y2 x3 y3"}]
                                 else [@{term "delta x2 y2 x3 y3"},@{term "delta_minus x2 y2 x3 y3"},@{term "delta_plus x2 y2 x3 y3"}]
 (*TODO: simple combinator for this*)
  val assms3 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_eq(@{term "z1'::'a \<times> 'a"},z1')))
  val assms4 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_eq(@{term "z3'::'a \<times> 'a"},z3')))
  val assms5 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta1 1,@{term "0::'a"}))))
  val assms6 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta1 2,@{term "0::'a"}))))
  val assms7 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta4 1,@{term "0::'a"}))))
  val assms8 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta4 2,@{term "0::'a"}))))
  val assms9 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta2 0,@{term "0::'a"}))))
  val assms10 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta2 1,@{term "0::'a"}))))
  val assms11 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta3 0,@{term "0::'a"}))))
  val assms12 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta3 1,@{term "0::'a"}))))

  val (assms,ctxt) = Assumption.add_assumes 
                         [@{cprop "z1' = (x1'::'a,y1'::'a)"}, @{cprop "z3' = (x3'::'a,y3'::'a)"},
                          assms3,assms4,assms5,assms6,assms7, assms8,assms9, assms10,assms11, assms12,
                          @{cprop "e x1 y1 = 0"}, @{cprop "e x2 y2 = 0"}, @{cprop "e x3 y3 = 0"} 
                         ] ctxt;

  val normalizex = List.foldl (HOLogic.mk_binop "Groups.times_class.times") @{term "1::'a"} [nth delta2 0, nth delta3 0, nth delta1 0, nth delta4 0] 
  val normalizey = List.foldl (HOLogic.mk_binop "Groups.times_class.times") @{term "1::'a"} [nth delta2 1, nth delta3 1, nth delta1 0, nth delta4 0]

  val fstminus = HOLogic.mk_binop "Groups.minus_class.minus"
                  (HOLogic.mk_fst (lhs @{term "z1'::'a \<times> 'a"}), HOLogic.mk_fst (rhs @{term "z3'::'a \<times> 'a"}))
  val sndminus = HOLogic.mk_binop "Groups.minus_class.minus" 
                  (HOLogic.mk_snd (lhs @{term "z1'::'a \<times> 'a"}), HOLogic.mk_snd (rhs @{term "z3'::'a \<times> 'a"}))
    
  val goal = HOLogic.mk_Trueprop(HOLogic.mk_eq(lhs z1',rhs z3'))

  val gxDeltax =
    HOLogic.mk_Trueprop(
     HOLogic.mk_exists ("r1",@{typ 'a},
      HOLogic.mk_exists("r2",@{typ 'a},
       HOLogic.mk_exists("r3",@{typ 'a},
        HOLogic.mk_eq(HOLogic.mk_binop "Groups.times_class.times" (fstminus,normalizex), 
                      @{term "r1 * e x1 y1 + r2 * e x2 y2 + r3 * e x3 y3"})))))

  val gyDeltay = 
    HOLogic.mk_Trueprop(
     HOLogic.mk_exists ("r1",@{typ 'a},
      HOLogic.mk_exists("r2",@{typ 'a},
       HOLogic.mk_exists("r3",@{typ 'a},
        HOLogic.mk_eq(HOLogic.mk_binop "Groups.times_class.times" (sndminus,normalizey), 
                      @{term "r1 * e x1 y1 + r2 * e x2 y2 + r3 * e x3 y3"})))))

  val (x1'_expr,y1'_expr,x3'_expr,y3'_expr) = basic_equalities assms ctxt z1' z3'
  val (rewrite1,rewrite2,rewrite3,rewrite4) = rewrite_procedures ctxt
 
  (* First subgoal *)
  val div1 = Goal.prove ctxt [] [] gxDeltax
   (fn _ => asm_full_simp_tac (ctxt addsimps [nth assms 0,nth assms 1]) 1
            THEN REPEAT rewrite1
            THEN asm_full_simp_tac (ctxt
                     addsimps (@{thms divide_simps} @ [nth assms 8, nth assms 10])) 1
            THEN REPEAT (EqSubst.eqsubst_tac ctxt [0] 
                (@{thms left_diff_distrib delta_x_def delta_y_def delta_minus_def delta_plus_def} @ [x1'_expr,y1'_expr,x3'_expr,y3'_expr]) 1)
            THEN simp_tac ctxt 1
            THEN REPEAT rewrite2
            THEN asm_full_simp_tac (ctxt
                     addsimps (@{thms divide_simps} @ map (nth assms) [4,5,6,7] @ 
                               [@{thm delta'_def}, @{thm delta_def}])) 1
            THEN asm_full_simp_tac (ctxt addsimps
                      [@{thm t_expr(1)},@{thm delta_x_def},
                       @{thm delta_y_def}, @{thm delta_plus_def}, 
                       @{thm delta_minus_def}, @{thm e_def}]) 1
            THEN Groebner.algebra_tac [] [] ctxt 1
   )                            

  val goal1 = HOLogic.mk_Trueprop (HOLogic.mk_eq (fstminus, @{term "0::'a"}))
  
  val eq1 = Goal.prove ctxt [] [] goal1
                (fn _ => Method.insert_tac ctxt [div1] 1
                        THEN asm_full_simp_tac (ctxt addsimps 
                            (map (nth assms) [4,5,6,7,8,10,12,13,14]) @ @{thms delta'_def delta_def}) 1 )
  
  val div2 = Goal.prove ctxt [] [] gyDeltay
   (fn _ => asm_full_simp_tac (@{context} addsimps [nth assms 0,nth assms 1]) 1
            THEN REPEAT rewrite3
            THEN asm_full_simp_tac (@{context} addsimps (@{thms divide_simps} @ [nth assms 9,nth assms 11])) 1
            THEN REPEAT (EqSubst.eqsubst_tac ctxt [0] (@{thms left_diff_distrib delta_x_def delta_y_def delta_minus_def delta_plus_def} @ [x1'_expr,y1'_expr,x3'_expr,y3'_expr]) 1)
            THEN simp_tac @{context} 1
                        THEN REPEAT rewrite4
            THEN asm_full_simp_tac (@{context}  addsimps (@{thms divide_simps delta'_def delta_def} @ (map (nth assms) [4,5,6,7]))) 1
            THEN asm_full_simp_tac (@{context} addsimps
                                [@{thm t_expr(1)},@{thm delta_x_def},
                                 @{thm delta_y_def}, @{thm delta_plus_def}, 
                                 @{thm delta_minus_def}, @{thm e_def}]) 1
            THEN Groebner.algebra_tac [] [] ctxt 1
   )

  val goal2 = HOLogic.mk_Trueprop (HOLogic.mk_eq (sndminus, @{term "0::'a"}))
  
  val eq2 = Goal.prove ctxt [] [] goal2
                (fn _ => Method.insert_tac ctxt [div2] 1
                        THEN asm_full_simp_tac (ctxt addsimps 
                            (map (nth assms) [4,5,6,7,9,11,12,13,14]) @ @{thms delta'_def delta_def}) 1 );
  
  val goal = Goal.prove ctxt [] [] goal
                (fn _ => Method.insert_tac ctxt ([eq1,eq2] @ [nth assms 2,nth assms 3]) 1
                        THEN asm_full_simp_tac ctxt 1 );  

in
 singleton (Proof_Context.export ctxt ctxt0) goal
end

\<close>


(* 
  Assume the following ordering: 2 1 3 4 
  TODO: change into 1 2 3 4, also remove the points theorems merge into one
*)
local_setup \<open>
  Local_Theory.note ((@{binding "add_add_add_add_assoc"}, []), [concrete_assoc "add" "add" "add" "add"]) #> snd 
\<close>

lemma add_add_add_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps ext_add.simps)
  using add_add_add_add_assoc 
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_ext_ext_assoc"}, []), [concrete_assoc "ext" "ext" "ext" "ext"]) #> snd 
\<close>

lemma ext_ext_ext_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "ext_add (ext_add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps ext_add.simps)
  using ext_ext_ext_ext_assoc 
  apply(safe) 
  by fastforce


local_setup \<open>
 Local_Theory.note ((@{binding "ext_add_ext_ext_assoc"}, []), [concrete_assoc "add" "ext" "ext" "ext"]) #> snd 
\<close>

lemma ext_add_ext_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "ext_add (add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps ext_add.simps)
  using ext_add_ext_ext_assoc 
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_ext_add_assoc"}, []), [concrete_assoc "ext" "ext" "ext" "add"]) #> snd 
\<close>

lemma ext_ext_ext_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "ext_add (ext_add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps ext_add.simps)
  using ext_ext_ext_add_assoc 
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_add_ext_assoc"}, []), [concrete_assoc "ext" "add" "add" "ext"]) #> snd 
\<close>

lemma add_ext_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_ext_add_ext_assoc 
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_ext_ext_assoc"}, []), [concrete_assoc "ext" "add" "ext" "ext"]) #> snd 
\<close>

lemma add_ext_ext_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (ext_add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using add_ext_ext_ext_assoc 
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_add_add_assoc"}, []), [concrete_assoc "ext" "add" "add" "add"]) #> snd 
\<close>

lemma add_ext_add_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_ext_add_add_assoc 
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "add_add_ext_add_assoc"}, []), [concrete_assoc "add" "add" "ext" "add"]) #> snd 
\<close>

lemma add_add_ext_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "add (add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_add_ext_add_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "add_add_ext_ext_assoc"}, []), [concrete_assoc "add" "add" "ext" "ext"]) #> snd 
\<close>

lemma add_add_ext_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using add_add_ext_ext_assoc
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "add_add_add_ext_assoc"}, []), [concrete_assoc "add" "add" "add" "ext"]) #> snd 
\<close>

lemma add_add_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_add_add_ext_assoc 
  apply(safe) 
  by (metis ext_add.simps prod.collapse)

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_add_ext_assoc"}, []), [concrete_assoc "add" "ext" "add" "ext"]) #> snd 
\<close>

lemma ext_add_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using ext_add_add_ext_assoc 
  apply(safe) 
  using prod.collapse ext_add.simps by metis

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_add_add_assoc"}, []), [concrete_assoc "add" "ext" "add" "add"]) #> snd 
\<close>

lemma ext_add_add_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using ext_add_add_add_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_ext_add_assoc"}, []), [concrete_assoc "add" "ext" "ext" "add"]) #> snd 
\<close>

lemma ext_add_ext_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "ext_add (add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using ext_add_ext_add_assoc
  apply(safe) 
  by fastforce

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_add_add_assoc"}, []), [concrete_assoc "ext" "ext" "add" "add"]) #> snd 
\<close>

lemma ext_ext_add_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using ext_ext_add_add_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_add_ext_assoc"}, []), [concrete_assoc "ext" "ext" "add" "ext"]) #> snd 
\<close>

lemma ext_ext_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using ext_ext_add_ext_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_ext_add_assoc"}, []), [concrete_assoc "ext" "add" "ext" "add"]) #> snd 
\<close>

lemma add_ext_ext_add_assoc_points:
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (ext_add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using add_ext_ext_add_assoc
  apply(safe) 
  by fastforce

lemma assoc_points:
  fixes x1 y1 l x2 y2 l' x3 y3 l''
  defines "sum1 == proj_add ((x1,y1),l) ((x2,y2),l')"
  defines "sum2 == proj_add ((x2,y2),l') ((x3,y3),l'')"
  assumes "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0 \<or> delta' x1 y1 x2 y2 \<noteq> 0" 
          "delta x2 y2 x3 y3 \<noteq> 0 \<or> delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (fst sum1)) (snd (fst sum1)) x3 y3 \<noteq> 0 \<or> delta' (fst (fst sum1)) (snd (fst sum1)) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (fst sum2)) (snd (fst sum2)) \<noteq> 0 \<or> delta' x1 y1 (fst (fst sum2)) (snd (fst sum2)) \<noteq> 0"
  shows "proj_add (proj_add ((x1,y1),l) ((x2,y2),l')) ((x3,y3),l'') = 
         proj_add ((x1,y1),l) (proj_add ((x2,y2),l') ((x3,y3),l''))"
  using assms 
  apply(elim disjE)
  using add_add_add_add_assoc_points add_closure apply auto[1]
  using add_add_ext_add_assoc_points add_closure apply auto[1]
  using ext_add_add_add_assoc_points add_closure apply auto[1]
  using ext_add_ext_add_assoc_points add_closure apply auto[1]
  using add_add_add_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using add_add_ext_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using ext_add_add_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using ext_add_ext_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using add_ext_add_add_assoc_points add_closure ext_add_closure apply auto[1]
  using add_ext_ext_add_assoc_points add_closure ext_add_closure apply auto[1]
  using ext_ext_add_add_assoc_points add_closure ext_add_closure apply auto[1]
  using ext_ext_ext_add_assoc_points add_closure ext_add_closure apply auto[1]
  using add_ext_add_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using add_ext_ext_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using ext_ext_add_ext_assoc_points add_closure ext_add_closure apply auto[1]
  using ext_ext_ext_ext_assoc_points add_closure ext_add_closure by auto[1]

lemma proj_add'_neutral:
  assumes "p \<in> e_aff"
  shows "proj_add' (p,l) ((1,0),l') = (p,l+l')"
proof -
  have "delta (fst p) (snd p) 1 0 \<noteq> 0"
    unfolding delta_def delta_plus_def delta_minus_def by auto
  then show ?thesis
    apply(cases "p",simp)
    by (metis assms e_proj_aff identity_equiv identity_proj add_neutral proj_add.simps(1))
qed

lemma proj_add'_inv:
  assumes "p \<in> e_aff"
  shows "proj_add' (p,l) (i p,l') = ((1,0),l+l')"
  using add_self assms proj_add_inv by(cases "p",simp) 

lemma proj_add'_comm:
  assumes "p \<in> e_aff" "q \<in> e_aff"
  shows "proj_add' (p,l) (q,l') = proj_add' (q,l') (p,l)"
proof -
  consider 
    (1) "delta (fst p) (snd p) (fst q) (snd q) \<noteq> 0 \<or> 
         delta' (fst p) (snd p) (fst q) (snd q) \<noteq> 0" |
    (2) "delta (fst p) (snd p) (fst q) (snd q) = 0" 
        "delta' (fst p) (snd p) (fst q) (snd q) = 0"
        "delta (fst p) (snd p) (fst (\<tau> q)) (snd (\<tau> q)) \<noteq> 0 \<or> 
         delta' (fst p) (snd p) (fst (\<tau> q)) (snd (\<tau> q)) \<noteq> 0" 
    using covering_with_deltas assms by(cases "p",cases "q",auto) 
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis 
      using proj_add_comm delta_com delta'_com assms
      by(cases "p",cases "q",auto) 
  next
    case 2
    have nz: "fst p \<noteq> 0" "snd p \<noteq> 0" "fst q \<noteq> 0" "snd q \<noteq> 0"
      using 2(1)
      unfolding delta_def delta_plus_def delta_minus_def
      by force+
    then have in_aff: "\<tau> p \<in> e_aff" "\<tau> q \<in> e_aff"
      using assms \<tau>_circ circ_to_aff e_circ_def by blast+
    from 2 show ?thesis 
      apply simp
      apply(cases "p",cases "q",simp del: \<tau>.simps)
      using proj_add_comm tau_idemp_explicit tau_tau_d tau_tau_d'
      by (smt \<tau>.simps ab_semigroup_add_class.add_ac(1) assms(1) assms(2) bit_add_eq_1_iff delta'_com delta_com ext_curve_addition.inversion_invariance_1 ext_curve_addition_axioms in_aff(1) in_aff(2) inversion_invariance_2 local.fstI local.sndI nz(1) nz(2) nz(3) nz(4) proj_add.simps(1) proj_add.simps(2) proj_add_comm tau_idemp_explicit tau_tau_d tau_tau_d')
  qed
qed

lemma rot_com_1:
  assumes "r \<in> rotations"
  shows "add (r p1) p2 = add p1 (r p2)"
  using add_comm assms rotation_invariance_1 by auto

lemma rot_com_2:
  assumes "r \<in> rotations"
  shows "ext_add (r p1) p2 = ext_add p1 (r p2)"
  using assms ext_add_comm rotation_invariance_2 by auto

lemma delta_rot:
  assumes "r \<in> rotations"
  shows "(delta x1 y1 x2 y2 = 0) =
         (delta x1 y1 (fst (r (x2,y2))) (snd (r (x2,y2))) = 0)" 
  using assms
  unfolding rotations_def delta_def delta_plus_def delta_minus_def
  apply simp 
  apply(elim disjE)
     apply simp_all
    apply(simp_all add: field_simps) 
  using eq_neg_iff_add_eq_0 by force+

lemma proj_add'_dich:
  assumes "q = ((\<tau> \<circ> r) \<circ> i) p" "p \<in> e_circ" "r \<in> rotations"
  shows "proj_add' (p,l) (q,l') = (r (1,0),l+l'+1)"
proof -
  obtain x1 y1 x2 y2 where p_q_expr: "p = (x1,y1)" "q = (x2,y2)" by fastforce
  
  have in_aff: "(x1,y1) \<in> e_aff" "i (x1,y1) \<in> e_aff" "r (i (x1,y1)) \<in> e_aff" "(x2,y2) \<in> e_aff"
    using assms(2) circ_to_aff p_q_expr(1) apply blast
    using assms(2) circ_to_aff i_aff p_q_expr(1) apply blast    
    using assms(2) assms(3) circ_to_aff i_aff p_q_expr(1) rot_aff apply blast
    using \<tau>_circ assms(1) assms(2) assms(3) circ_to_aff i_circ_points p_q_expr(2) rot_circ by auto
  let ?canadd = "\<lambda> p q. delta (fst p) (snd p) (fst q) (snd q) \<noteq> 0 \<or>
                        delta' (fst p) (snd p) (fst q) (snd q) \<noteq> 0"
  have ds: "delta x1 y1 x2 y2 = 0" "delta' x1 y1 x2 y2 = 0"
    using p_q_expr wd_d_nz wd_d'_nz tau_rot_sym assms by fastforce+
  have ds': "?canadd (x1,y1) (i (x1,y1))"  
    using add_self in_aff(1) by auto
  then have ds'': "?canadd (x1,y1) (r (i (x1,y1)))" 
    by (metis assms(1) comp_apply covering_with_deltas ds(1) ds(2) fst_conv in_aff(1) in_aff(3) p_q_expr(1) p_q_expr(2) snd_conv surjective_pairing)

  from ds have "proj_add' ((x1,y1),l) ((x2,y2),l') = 
                proj_add ((x1,y1),l) (\<tau> (x2,y2),l'+1)"
    by simp
  also have "... = proj_add ((x1,y1),l) (r (i (x1,y1)),l'+1)"
    using assms(1) p_q_expr(1) p_q_expr(2) tau_idemp_point by auto
  also have "... = (r (1,0),l+l'+1)"
    using tf_proj_add'_rot[OF in_aff(2,1) assms(3),of "l'+1" l] 
          proj_add'_comm proj_add'_inv[OF in_aff(1), of l "l'+1"] 
    by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) ds'' in_aff(1) in_aff(2) in_aff(3) local.fstI local.sndI prod.collapse proj_add'.simps)
  finally show ?thesis using p_q_expr by auto
qed

lemma proj_add'_neutral_rot:
  assumes "r \<in> rotations" "q \<in> e_aff"
  shows "proj_add' (r (1,0),l) (q,l') = (r q,l+l')"
proof -
  have in_aff: "(1,0) \<in> e_aff" 
    using e_proj_aff identity_equiv identity_proj by force
  have "proj_add' (r (1,0),l) (q,l') = (r (fst (proj_add' ((1, 0), l) (q, l'))), snd (proj_add' ((1, 0), l) (q, l')))" 
    using tf_proj_add'_rot[OF in_aff assms(2,1), of l l'] by auto
  also have "... = (r q,l+l')"
    using proj_add'_neutral[OF assms(2), of l l'] 
          proj_add'_comm[OF assms(2) in_aff, of l l']  
    by (simp add: \<open>proj_add' (q, l) ((1, 0), l') = (q, l + l')\<close> assms(2) ext_curve_addition.proj_add'_comm ext_curve_addition.proj_add'_neutral ext_curve_addition_axioms in_aff)  
  finally show ?thesis by auto
qed

lemmas deltas = (* TODO: rewrite unfoldings *)
delta_def delta_minus_def delta_plus_def 
delta'_def delta_x_def delta_y_def

subsection \<open>Lemmas for associativity\<close>

lemma cancellation_assoc:
  assumes "\<langle>((x1,y1),0)\<rangle> \<in> e_proj" "\<langle>((x2,y2),0)\<rangle> \<in> e_proj" "\<langle>(i (x2,y2),0)\<rangle> \<in> e_proj"
  shows "(\<langle>((x1,y1),0)\<rangle> \<oplus> \<langle>((x2,y2),0)\<rangle>) \<oplus> (\<langle>(i (x2,y2),0)\<rangle>) = \<langle>((x1,y1),0)\<rangle>"
  (is "(?g1 \<oplus> ?g2) \<oplus> ?g3 = ?g1")
proof - 
  have in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "i (x2,y2) \<in> e_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have one_in: "\<langle>((1, 0), 0)\<rangle> \<in> e_proj"
    using identity_proj identity_equiv by auto

  have e_proj: "\<langle>((x1, y1), 0)\<rangle> \<in> e_proj" "\<langle>((x2, y2), 0)\<rangle> \<in> e_proj"
               "\<langle>(i (x1, y1), 0)\<rangle> \<in> e_proj" "{((1, 0), 0)} \<in> e_proj"
               "\<langle>(i (x2, y2), 0)\<rangle> \<in> e_proj"                   
    using e_proj_aff in_aff apply(simp,simp)
    using assms proj_add_class_inv apply blast
    using identity_equiv one_in apply auto[1]
    using assms(2) proj_add_class_inv by blast
  
  consider (1) "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" | (2) "x1 = 0 \<or> y1 = 0 \<or> x2 = 0 \<or> y2 = 0" by fastforce
  then show ?thesis
  proof(cases)
    case 1
    have taus: "\<tau> (i (x2, y2)) \<in> e_aff"
    proof -
      have "i (x2,y2) \<in> e_circ"
        using e_circ_def in_aff 1 by auto
      then show ?thesis
        using \<tau>_circ circ_to_aff by blast
    qed
     
    consider
      (a) "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))" "(x1,y1) \<in> e_circ" |
      (b) "((x1, y1), x2, y2) \<in> e_aff_0 \<or> ((x1, y1), x2, y2) \<in> e_aff_1" 
          "\<not> ((\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1)) \<and> (x1,y1) \<in> e_circ)" 
        using dichotomy_1 in_aff by blast
    then show ?thesis 
    proof(cases)
      case a 
      assume "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))" 
      then obtain g where g_expr: "g \<in> symmetries" "(x2, y2) = (g \<circ> i) (x1, y1)" by auto
      then obtain g' where g_expr': "g' \<in> symmetries" "i (x2,y2) = g' (x1, y1)" "g \<circ> g' = id"
        using symmetries_i_inverse[OF g_expr(1), of x1 y1] 
              i_idemp pointfree_idE by force      
    
      obtain r where r_expr: "r \<in> rotations" "(x2, y2) = (\<tau> \<circ> r) (i (x1, y1))" "g = \<tau> \<circ> r"
        using g_expr sym_decomp by force
                
      have e_proj_comp: "\<langle>(g (i (x1, y1)), 0)\<rangle> \<in> e_proj" 
                        "\<langle>(g (i (x2, y2)), 0)\<rangle> \<in> e_proj"
        using assms g_expr apply force
        using assms g_expr' g_expr' pointfree_idE by fastforce

      have "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>(r (1,0),1)\<rangle> \<oplus> ?g3" 
        by (metis (no_types, lifting) a(2) bit_add_eq_1_iff e_proj(1) e_proj(2) ext_curve_addition.independence ext_curve_addition.proj_add'_dich ext_curve_addition_axioms g_expr(2) r_expr(1) r_expr(3))
      also have "... = \<langle>proj_add' (r (1,0),1) (i (x2, y2), 0)\<rangle>"
        using independence e_proj_aff
        by (metis (no_types, lifting) assms(3) i.simps one_in prod.collapse r_expr(1) rot_aff)
      also have "... = \<langle>(r (i (x2, y2)), 1)\<rangle>"
        using proj_add'_neutral_rot  in_aff(3) r_expr(1) by auto
      also have "... = \<langle>(\<tau> (r (i (x2, y2))), 0)\<rangle>"
        using tf_tau remove_tau
        by (metis (no_types, lifting) add_cancel_left_left comp_def e_proj(5) e_proj_aff e_proj_comp(2) r_expr(1) r_expr(3) rot_aff)
      also have "... = ?g1"
        using g_expr'(2) g_expr'(3) pointfree_idE r_expr(3) by fastforce
      finally show ?thesis by auto
    next
      case b      
      have pd: "delta x1 y1 x2 y2 \<noteq> 0 \<or> delta' x1 y1 x2 y2 \<noteq> 0"
        using b unfolding e_aff_0_def e_aff_1_def by auto

      have ds: "delta x2 y2 x2 (-y2) \<noteq> 0 \<or> delta' x2 y2 (x2) (-y2) \<noteq> 0 "
        using add_self in_aff(2) by blast
  
      have eq1: "?g1 \<oplus> ?g2 = \<langle>proj_add' ((x1,y1),0) ((x2,y2),0)\<rangle>"
        (is "_ = \<langle>?g_add\<rangle>")
        by (simp add: e_proj(1) e_proj(2) independence)        
      then obtain rx ry where r_expr: 
        "rx = fst (fst (?g_add))"  "ry = snd (fst (?g_add))" "(rx,ry) = fst (?g_add)"
        by simp
      have in_aff_r: "(rx,ry) \<in> e_aff"
        by (metis e_proj(1) e_proj(2) e_proj_aff independence prod.collapse r_expr(3) well_defined)
      have e_proj_r: "\<langle>((rx,ry), 0)\<rangle> \<in> e_proj"
        using e_proj_aff in_aff_r by auto
                
      consider
        (aa) "(rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry))" |
        (bb) "((rx, ry), i (x2, y2)) \<in> e_aff_0 \<or> ((rx, ry), i (x2, y2)) \<in> e_aff_1" 
             "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry)))" 
        using dichotomy_1[OF in_aff_r in_aff(3)] by fast        
      then show ?thesis 
      proof(cases)
        case aa 
        have ds': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) = 0"
                  "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) = 0"
          using aa wd_d_nz wd_d'_nz by auto
        show ?thesis
          apply(cases "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0 \<or> 
                       delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0")
          apply(elim disjE)
          using delta'_add_delta_2[OF 1,of rx ry] delta_add_delta'_1[OF 1,of rx ry] ds'
                in_aff(1) in_aff(2) pd r_expr(3) apply auto[1]
          using delta_add_delta'_2[OF 1,of rx ry] delta'_add_delta_1[OF 1,of rx ry] ds' 
                in_aff(1) in_aff(2) pd r_expr(3) apply auto[1]
          using covering_with_deltas ds'(1) ds'(2) in_aff(3) in_aff_r by fastforce
      next
        case bb        
        then have pd': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0 \<or>
                        delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
          using bb unfolding e_aff_0_def e_aff_1_def r_expr by force
        
        have f1: "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>proj_add' ((proj_add' ((x1,y1),0)) ((x2,y2),0)) (i (x2,y2),0)\<rangle>"
          by (metis eq1 e_proj(1) e_proj(2) e_proj(5) independence prod.collapse well_defined)
        have f3: "proj_add ((x2,y2),0) (i (x2,y2),0) = ((1,0),0)"
          using in_aff(2) proj_add_inv by auto
        have "proj_add' ((proj_add' ((x1,y1),0)) ((x2,y2),0)) (i (x2,y2),0) =
              proj_add ((proj_add ((x1,y1),0)) ((x2,y2),0)) (i (x2,y2),0)"
          using ds pd pd' r_expr by (smt prod.collapse proj_add'.simps)
        also have "... = proj_add ((x1,y1),0) (proj_add ((x2,y2),0) (i (x2,y2),0))"
          apply(rule assoc_points[OF in_aff(1,2), of "fst (i (x2,y2))" "snd (i (x2,y2))",
                             simplified prod.collapse, OF in_aff(3), of 0 0])
          using pd apply blast
          using ds apply auto[1]
          using pd pd' r_expr(1) r_expr(2) apply auto[1]
          using f3 apply simp unfolding delta_def delta_plus_def delta_minus_def by force
        also have "... = ((x1,y1),0)"
        proof(rewrite f3)
          have "(1,0) \<in> e_aff" "delta x1 y1 1 0 \<noteq> 0"
            using e_proj_aff one_in apply blast
            unfolding delta_def delta_plus_def delta_minus_def by auto
          then show "proj_add ((x1, y1), 0) ((1, 0), 0) = ((x1, y1), 0)"
            using add_neutral ext_add_neutral 1 in_aff(1) by simp 
        qed
        finally show ?thesis using f1 by auto
      qed
    qed
  next
    case 2
    then have "(\<exists> r \<in> rotations. (x1,y1) = r (1,0)) \<or> (\<exists> r \<in> rotations. (x2,y2) = r (1,0))"
      using in_aff(1,2) unfolding e_aff_def e_def 
      apply(safe)
      unfolding rotations_def
      by(simp,algebra)+
    then consider
      (a) "(\<exists> r \<in> rotations. (x1,y1) = r (1,0))" | 
      (b) "(\<exists> r \<in> rotations. (x2,y2) = r (1,0))" by argo      
    then show ?thesis 
    proof(cases)
      case a
      then obtain r where rot_expr: "r \<in> rotations" "(x1, y1) = r (1, 0)" by blast
      have "(\<langle>((x1, y1), 0)\<rangle> \<oplus> \<langle>((x2, y2), 0)\<rangle>) \<oplus> \<langle>(i (x2, y2), 0)\<rangle> = 
            \<langle>proj_add' ((x1, y1), 0) ((x2, y2), 0)\<rangle> \<oplus> \<langle>(i (x2, y2), 0)\<rangle>"
        by (simp add: e_proj(1) e_proj(2) independence)
      also have "... = \<langle>(r (x2,y2), 0)\<rangle> \<oplus> \<langle>(i (x2, y2), 0)\<rangle>"
        by (simp add: in_aff(2) proj_add'_neutral_rot rot_expr(1) rot_expr(2))
      also have "... = \<langle>(r (1,0), 0)\<rangle>"
        by (metis (no_types, lifting) add_cancel_left_left e_proj(2) e_proj(5) identity_equiv one_in proj_add_class_inv(1) remove_add_rotation remove_rotations rot_expr(1))
      also have "... = \<langle>((x1, y1), 0)\<rangle>"
        by (simp add: rot_expr(2))
      finally show ?thesis by auto
    next
      case b
      then obtain r where rot_expr: "r \<in> rotations" "(x2, y2) = r (1, 0)" by blast
      then obtain r' where rot_expr': "r' \<in> rotations" "i (x2, y2) = r' (1, 0)" "r \<circ> r' = id" 
        using rotations_i_inverse[OF rot_expr(1),of "r (1,0)"]
        by (metis (no_types, hide_lams) comp_apply diff_0 diff_zero i.simps id_apply rot_inv)
      have "(\<langle>((x1, y1), 0)\<rangle> \<oplus> \<langle>((x2, y2), 0)\<rangle>) \<oplus> \<langle>(i (x2, y2), 0)\<rangle> = 
            \<langle>(r (x1, y1), 0)\<rangle> \<oplus> \<langle>(i (x2, y2), 0)\<rangle>"
        by (metis (no_types, hide_lams) add_cancel_left_left e_proj(1) e_proj(2) ext_curve_addition.independence ext_curve_addition_axioms in_aff(1) proj_add'_neutral_rot proj_addition_comm rot_expr(1) rot_expr(2))
      also have "... = \<langle>proj_add' (r (x1, y1), 0) (r' (1, 0), 0)\<rangle>"
        using rot_expr'(2) 
        by (metis (no_types, lifting) e_proj(5) e_proj_aff i.simps in_aff(1) independence prod.collapse rot_aff rot_expr(1))
      also have "... = \<langle>(r' (r (x1, y1)), 0)\<rangle>"
        using proj_add'_neutral_rot[OF \<open>r' \<in> rotations\<close>, of "r (x1, y1)" 0 0]
              proj_add'_comm in_aff(1) in_aff(3) rot_aff rot_expr'(2) rot_expr(1) by auto 
      also have "... = \<langle>((x1, y1), 0)\<rangle>"
        by (metis comp_apply rot_com rot_expr'(1) rot_expr'(3) rot_expr(1) tau_idemp tau_sq)
      finally show ?thesis by auto
    qed
  qed
qed

lemma cancellation_assoc_points:
  assumes "\<langle>(p,0)\<rangle> \<in> e_proj" "\<langle>(q,0)\<rangle> \<in> e_proj" "\<langle>(i q,0)\<rangle> \<in> e_proj"
  shows "(\<langle>(p,0)\<rangle> \<oplus> \<langle>(q,0)\<rangle>) \<oplus> (\<langle>(i q,0)\<rangle>) = \<langle>(p,0)\<rangle>"
  using cancellation_assoc assms by(cases "p",cases "q",auto) 

lemma e_aff_0_invariance:
  "(p,q) \<in> e_aff_0 \<Longrightarrow> (q,p) \<in> e_aff_0"
  unfolding e_aff_0_def deltas
  by (cases "p",cases "q",simp add: algebra_simps)

lemma e_aff_1_invariance:
  "(p,q) \<in> e_aff_1 \<Longrightarrow> (q,p) \<in> e_aff_1"
  unfolding e_aff_1_def deltas
  by(cases "p",cases "q",simp add: algebra_simps,argo)   

lemma assoc_with_zeros:
  assumes "\<langle>((x1, y1), 0)\<rangle> \<in> e_proj" "\<langle>((x2, y2), 0)\<rangle> \<in> e_proj" "\<langle>((x3, y3), 0)\<rangle> \<in> e_proj"
  shows "((\<langle>((x1, y1), 0)\<rangle> \<oplus> \<langle>((x2, y2), 0)\<rangle>) \<oplus> \<langle>((x3, y3), 0)\<rangle>) = 
         (\<langle>((x1, y1), 0)\<rangle> \<oplus> (\<langle>((x2, y2), 0)\<rangle> \<oplus> \<langle>((x3, y3), 0)\<rangle>))"
  (is "(?g1 \<oplus> ?g2) \<oplus> ?g3 = (?g1 \<oplus> (?g2 \<oplus> ?g3))")
proof -
  have in_aff: "(x1,y1) \<in> e_aff" "(x2,y2) \<in> e_aff" "(x3,y3) \<in> e_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have e_proj_0: "\<langle>(i (x1,y1), 0)\<rangle> \<in> e_proj" (is "?ig1 \<in> e_proj")
                 "\<langle>(i (x2,y2), 0)\<rangle> \<in> e_proj" (is "?ig2 \<in> e_proj")
                 "\<langle>(i (x3,y3), 0)\<rangle> \<in> e_proj" (is "?ig3 \<in> e_proj")    
    using assms proj_add_class_inv by auto
 
  consider
    (1) "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))" "(x1,y1) \<in> e_circ" |
    (2) "((x1, y1), x2, y2) \<in> e_aff_0 \<or> ((x1, y1), x2, y2) \<in> e_aff_1" 
        "\<not> ((\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1)) \<and> (x1,y1) \<in> e_circ)" 
    using dichotomy_1 in_aff by blast
  then show ?thesis
  proof(cases)
    case 1
    then obtain g where g_expr: "g \<in> symmetries" "(x2, y2) = (g \<circ> i) (x1, y1)" by blast
    then obtain r where r_expr: "r \<in> rotations" "g = \<tau> \<circ> r" using sym_decomp by blast

    have "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>(r (1,0),1)\<rangle> \<oplus> ?g3"
      using proj_add'_dich  "1"(2) assms(1) assms(2) g_expr(2) independence_points r_expr(1) r_expr(2) by auto
    also have "... = \<langle>(r (x3,y3),1)\<rangle>"
      using proj_add'_neutral_rot 
      by (metis (no_types, lifting) add.right_neutral e_proj_aff identity_equiv identity_proj in_aff(3) independence_points r_expr(1) rot_aff)
    finally have eq1: "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>(r (x3,y3),1)\<rangle>" by auto

    have "?g1 \<oplus> (?g2 \<oplus> ?g3) =  ?g1 \<oplus> (\<langle>((\<tau> \<circ> r \<circ> i) (x1, y1),0)\<rangle> \<oplus> ?g3)"
      by (simp add: g_expr(2) r_expr(2))
    also have "... = tf'' r (?g1 \<oplus> (\<langle>(i (x1,y1),0)\<rangle> \<oplus> ?g3))"
      by (smt assms(1) assms(2) assms(3) comp_def e_proj_0(1) ext_curve_addition.get_sym ext_curve_addition_axioms g_expr(2) r_expr(1) r_expr(2) remove_add_rot remove_add_rot_comm well_defined)
    also have "... = tf'' r \<langle>((x3,y3),0)\<rangle>"
      by (metis (no_types, lifting) assms(1) assms(3) cancellation_assoc_points e_proj_0(1) i_idemp_explicit proj_addition_comm well_defined)
    also have "... = \<langle>(r (x3,y3),1)\<rangle>"
      by (simp add: e_proj_aff in_aff(3) r_expr(1) remove_rotations rot_aff tf''_def tf_tau)
    finally have eq2: "?g1 \<oplus> (?g2 \<oplus> ?g3) = \<langle>(r (x3,y3),1)\<rangle>" by auto
    
    then show ?thesis using eq1 eq2 by auto
  next
    case 2
    have p_delta_1_2: "delta x1 y1 x2 y2 \<noteq> 0 \<or> delta' x1 y1 x2 y2 \<noteq> 0"
                      "delta (fst (i (x1, y1))) (snd (i (x1, y1))) (fst (i (x2, y2))) (snd (i (x2, y2))) \<noteq> 0 \<or>
                       delta' (fst (i (x1, y1))) (snd (i (x1, y1))) (fst (i (x2, y2))) (snd (i (x2, y2))) \<noteq> 0" 
        using 2 unfolding e_aff_0_def e_aff_1_def apply fast
        using 2 in_aff unfolding e_aff_0_def e_aff_1_def deltas by auto

    let ?add_1_2 = "fst (proj_add ((x1, y1),0) ((x2, y2),0))" 
    have add_in_1_2: "?add_1_2 \<in> e_aff"
      using add_closure ext_add_closure e_aff_def in_aff p_delta_1_2 by auto

    have e_proj_1_2: "\<langle>(?add_1_2,0)\<rangle> \<in> e_proj" "\<langle>(i ?add_1_2,0)\<rangle> \<in> e_proj" 
      using add_in_1_2 e_proj_aff proj_add_class_inv by(cases ?add_1_2,auto)
      
    consider
      (11) "(\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2))" "(x2,y2) \<in> e_circ" |
      (22) "((x2, y2), (x3, y3)) \<in> e_aff_0 \<or> ((x2, y2), (x3, y3)) \<in> e_aff_1" 
            "\<not> ((\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2)) \<and> (x2,y2) \<in> e_circ)" 
      using dichotomy_1 in_aff by blast
    then show ?thesis 
    proof(cases)
      case 11
      then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) (x2, y2)" by blast
      then obtain r where r_expr: "r \<in> rotations" "g = \<tau> \<circ> r" using sym_decomp by blast
      
      have "?g1 \<oplus> (?g2 \<oplus> ?g3) = ?g1 \<oplus> \<langle>(r (1,0),1)\<rangle>"
        using proj_add'_dich[OF _ 11(2) r_expr(1), of "(x3,y3)" 0 0] 
              g_expr r_expr assms(2) assms(3) independence_points by auto
      also have "... = \<langle>(r (x1,y1),1)\<rangle>"
        using proj_add'_neutral_rot proj_add'_comm 
        by (metis (no_types, hide_lams) add_cancel_left_right assms(1) e_proj_aff identity_equiv identity_proj independence_points r_expr(1) rot_aff)
      finally have eq1: "?g1 \<oplus> (?g2 \<oplus> ?g3) = \<langle>(r (x1,y1),1)\<rangle>" by auto

      have "(?g1 \<oplus> ?g2) \<oplus> ?g3 = (?g1 \<oplus> ?g2) \<oplus> \<langle>((\<tau> \<circ> r \<circ> i) (x2,y2),0)\<rangle>"
        using g_expr by (simp add: r_expr(2))
      also have "... = tf'' r ((?g1 \<oplus> ?g2) \<oplus> \<langle>(i (x2,y2),0)\<rangle>)"
        using e_proj_0(2) e_proj_aff g_expr(2) get_sym in_aff(1) in_aff(2) in_aff(3) r_expr(1) r_expr(2) remove_add_rot_comm well_defined by auto
      also have "... = tf'' r \<langle>((x1,y1),0)\<rangle>"
        using cancellation_assoc_points assms(1) assms(2) e_proj_0(2) by auto
      also have "... = \<langle>(r (x1,y1),1)\<rangle>"
        by (simp add: e_proj_aff in_aff(1) r_expr(1) remove_rotations rot_aff tf''_def tf_tau)
      finally have eq2: "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>(r (x1,y1),1)\<rangle>" by auto

      show ?thesis using eq1 eq2 by auto
    next
      case 22
      have p_delta_2_3: "delta x2 y2 x3 y3 \<noteq> 0 \<or> delta' x2 y2 x3 y3 \<noteq> 0"
                    "delta (fst (i (x2,y2))) (snd (i (x2,y2))) (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0 \<or>
                     delta' (fst (i (x2,y2))) (snd (i (x2,y2))) (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 22 unfolding e_aff_0_def e_aff_1_def apply fast
        using 22 unfolding e_aff_0_def e_aff_1_def deltas by force

      let ?add_2_3 = "fst (proj_add ((x2,y2),0) ((x3,y3),0))"
      have add_in_2_3: "?add_2_3 \<in> e_aff"
        using add_closure ext_add_closure e_aff_def in_aff p_delta_2_3 by auto

      have e_proj_2_3: "\<langle>(?add_2_3,0)\<rangle> \<in> e_proj" "\<langle>(i ?add_2_3,0)\<rangle> \<in> e_proj" 
        using add_in_2_3 e_proj_aff proj_add_class_inv by(cases "?add_2_3",auto) 

      consider
        (111) "(\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) ?add_2_3)" "?add_2_3 \<in> e_circ" |
        (222) "(?add_2_3, (x1,y1)) \<in> e_aff_0 \<or> (?add_2_3, (x1,y1)) \<in> e_aff_1" 
              "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) ?add_2_3) \<and> ?add_2_3 \<in> e_circ)" 
        using add_in_2_3 in_aff dichotomy_1 by blast        
      then show ?thesis   
      proof(cases)
        case 111       
        let ?add_2_3 = "fst (proj_add ((x2,y2),0) ((x3,y3),0))"
        from 111 obtain g where g_expr: "g \<in> symmetries" "(x1,y1) = (g \<circ> i) ?add_2_3" by blast
        then obtain r where r_expr: "r \<in> rotations" "\<tau> \<circ> r = g" using sym_decomp by blast
        
        have e_proj_2_3_g: "\<langle>((r \<circ> i) ?add_2_3, 1)\<rangle> \<in> e_proj" 
                           "\<langle>((g \<circ> i) ?add_2_3, 1)\<rangle> \<in> e_proj" 
          apply(simp add: add_in_2_3 e_proj_aff i_aff r_expr rot_aff)
          using e_proj_aff g_expr(2) in_aff(1) by auto

        have "?g1 \<oplus> (?g2 \<oplus> ?g3) = \<langle>((g \<circ> i) ?add_2_3, 0)\<rangle> \<oplus> (?g2 \<oplus> ?g3)" 
          using g_expr by simp
        also have "... = \<langle>((g \<circ> i) ?add_2_3, 0)\<rangle> \<oplus> \<langle>(?add_2_3, 0)\<rangle>" 
          using p_delta_2_3 assms(2,3) independence in_aff(2) in_aff(3) by auto
        also have "... = \<langle>((r \<circ> i) ?add_2_3, 1)\<rangle> \<oplus> \<langle>(?add_2_3, 0)\<rangle>" 
          using remove_tau tf_tau e_proj_2_3_g 
          by (metis bit_add_self comp_def r_expr(2) tau_idemp_point)
        also have "... = \<langle>proj_add' ((r \<circ> i) ?add_2_3, 1) (?add_2_3, 0)\<rangle>"
          using independence_points e_proj_2_3(1) e_proj_2_3_g(1) by blast
        also have "... = \<langle>(\<lambda> p. (r (fst p),snd p)) (proj_add' (i ?add_2_3, 1) (?add_2_3, 0))\<rangle>"
          using tf_proj_add'_rot by (simp add: add_in_2_3 i_aff r_expr(1))
        also have "... = \<langle>(r (1,0),1)\<rangle>"
          by (simp add: add_in_2_3 proj_add'_comm proj_add'_inv i_aff)
        finally have eq1: "?g1 \<oplus> (?g2 \<oplus> ?g3) = \<langle>(r (1,0),1)\<rangle>" by auto

        have "(?g1 \<oplus> ?g2) \<oplus> ?g3 = (\<langle>((\<tau> \<circ> r \<circ> i) ?add_2_3, 0)\<rangle> \<oplus> ?g2) \<oplus> ?g3"
          using g_expr r_expr by argo 
        also have "... = tf'' r ((\<langle>(i ?add_2_3, 0)\<rangle> \<oplus> ?g2) \<oplus> ?g3)"
          by (smt assms(1) assms(2) assms(3) comp_def e_proj_2_3(2) g_expr(2) get_sym r_expr(1) r_expr(2) remove_add_rot well_defined)
        also have "... = tf'' r ((\<langle>proj_add (i (x2,y2),0) (i (x3,y3),0)\<rangle> \<oplus> ?g2) \<oplus> ?g3)"
        proof(cases "delta x2 y2 x3 y3 \<noteq> 0")
          assume as: "delta x2 y2 x3 y3 \<noteq> 0"
          then have as': "delta x2 (-y2) x3 (-y3) \<noteq> 0"
            unfolding deltas by auto
          then have "i ?add_2_3 = (add (i (x2,y2)) (i (x3,y3)))"
            using inverse_rule_3 as in_aff(2,3) by force
          also have "... = fst (proj_add (i (x2, y2), 0) (i (x3, y3), 0))"
            using as' in_aff(2,3) i_aff by auto
          finally have "i ?add_2_3 = fst (proj_add (i (x2, y2), 0) (i (x3, y3), 0))" by auto
          then show ?thesis using as' i_aff in_aff(2) in_aff(3) by force
        next
          assume as: "\<not> delta x2 y2 x3 y3 \<noteq> 0"
          then have "delta' x2 y2 x3 y3 \<noteq> 0"
            using p_delta_2_3 by auto
          then have as': "delta' x2 (-y2) x3 (-y3) \<noteq> 0" 
            unfolding deltas by auto
          then have "i ?add_2_3 = (ext_add (i (x2,y2)) (i (x3,y3)))"
            using inverse_rule_4 as in_aff(2,3) p_delta_2_3(1) by auto
          also have "... = fst (proj_add (i (x2, y2), 0) (i (x3, y3), 0))"
            using as' in_aff(2,3) i_aff by auto
          finally have "i ?add_2_3 = fst (proj_add (i (x2, y2), 0) (i (x3, y3), 0))" by auto
          then show ?thesis using as' i_aff in_aff(2) in_aff(3) by force
        qed
        also have "... = tf'' r (((\<langle>(i (x2,y2),0)\<rangle> \<oplus> \<langle>(i (x3,y3),0)\<rangle>) \<oplus> ?g2) \<oplus> ?g3)"
          using e_proj_0(2) e_proj_0(3) independence_points p_delta_2_3(2) by auto
        also have "... = tf'' r (\<langle>(i (x3,y3),0)\<rangle> \<oplus> ?g3)"
          by (metis assms(2) cancellation_assoc e_proj_0(2) e_proj_0(3) i.simps i_idemp_explicit proj_addition_comm)
        also have "... = tf'' r \<langle>((1,0),0)\<rangle>"
          by (metis add_cancel_left_left assms(3) e_proj_0(3) proj_addition_comm identity_equiv proj_add_class_inv(1))
        also have "... = \<langle>(r (1,0),1)\<rangle>"
          by (smt add_neg_numeral_special(7) bit_minus1 e_proj_aff identity_equiv identity_proj r_expr(1) remove_rotations rot_aff tf''_def tf'_idemp tf_tau)
        finally have eq2: "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>(r (1,0),1)\<rangle>" by auto

        show ?thesis using eq1 eq2 by auto
      next
        case 222
        have in_aff_i: "((x1, y1),?add_2_3) \<in> e_aff_0 \<or> ((x1, y1),?add_2_3) \<in> e_aff_1" 
          using 222 e_aff_0_invariance e_aff_1_invariance by blast
        then have p_delta_i: "delta x1 y1 (fst ?add_2_3) (snd ?add_2_3) \<noteq> 0 \<or>
                              delta' x1 y1 (fst ?add_2_3) (snd ?add_2_3) \<noteq> 0"
          unfolding e_aff_0_def e_aff_1_def by auto 
        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) ?add_1_2)" "?add_1_2 \<in> e_circ" |
          (2222) "(?add_1_2, (x3,y3)) \<in> e_aff_0 \<or> (?add_1_2, (x3,y3)) \<in> e_aff_1" 
                 "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) ?add_1_2) \<and> ?add_1_2 \<in> e_circ)" 
          using add_in_1_2 in_aff dichotomy_1 by blast
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) ?add_1_2" by blast
          then obtain r where rot: "r \<in> rotations" "r = \<tau> \<circ> g" using sym_to_rot assms by blast

          have add_1: "\<langle>((x1,y1),0)\<rangle> \<oplus> \<langle>((x2,y2),0)\<rangle> = \<langle>(?add_1_2,0)\<rangle>"
            using independence assms in_aff p_delta_1_2(1) by auto
          have add_2: "?ig1 \<oplus> ?ig2 = \<langle>(i ?add_1_2,0)\<rangle>"
            using independence_points[OF e_proj_0(1,2)] 
                  p_delta_1_2(2) inverse_rule_3 inverse_rule_4 
            by (metis (no_types, lifting) add_1 assms(1) assms(2) cancellation_assoc e_proj_0(1) e_proj_0(2) e_proj_1_2(1) e_proj_1_2(2) prod.collapse proj_addition_comm)

          have "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>proj_add' ((x1,y1),0) ((x2,y2),0)\<rangle> \<oplus> ?g3"
            by (simp add: assms(1) assms(2) independence_points)
          also have "... = \<langle>(r (1,0),1)\<rangle>"
            using proj_add'_dich[OF _ 1111(2) rot(1), of "(x3,y3)" 0 0] rot(2) g_expr(2)
            by (metis (no_types, lifting) add_1 add_cancel_left_left assms(1) assms(2) assms(3) comp_def e_proj_1_2(1) independence_points tau_sq)
          finally have eq1: "(?g1 \<oplus> ?g2) \<oplus> ?g3  = \<langle>(r (1,0),1)\<rangle>" by auto
          
          have "?g1 \<oplus> (?g2 \<oplus> ?g3) = (?g1 \<oplus> (?g2 \<oplus> (\<langle>(g (i ?add_1_2), 0)\<rangle>)))"
            using g_expr by auto          
          also have "... =  (?g1 \<oplus> (tf'' r (\<langle>(i ?add_1_2,0)\<rangle> \<oplus> ?g2)))" 
            by (smt assms(2) assms(3) comp_def e_proj_1_2(2) proj_addition_comm remove_add_rot g_expr(2) get_sym id_comp o_assoc rot tau_idemp)
          also have "... = (?g1 \<oplus> (tf'' r ((?ig1 \<oplus> ?ig2) \<oplus> ?g2)))"
            using add_2 by simp
          also have "... = proj_addition ?g1 (tf'' r ?ig1)"
            by (metis assms(2) e_proj_0(1) e_proj_0(2) cancellation_assoc_points i_idemp_explicit)
          also have "... = tf'' r (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_rot rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' r ({((1, 0), 0)})"
            using assms(1) proj_add_class_comm proj_add_class_inv by auto
          also have "... = \<langle>(r (1,0),1)\<rangle>"
            by (smt add_neg_numeral_special(7) bit_minus1 e_proj_aff ext_curve_addition.remove_rotations ext_curve_addition_axioms identity_equiv identity_proj rot(1) rot_aff tf''_def tf'_idemp tf_tau)
          finally have eq2: "?g1 \<oplus> (?g2 \<oplus> ?g3) = \<langle>(r (1,0),1)\<rangle>" by auto
          
          show ?thesis using eq1 eq2 by auto
        next
          case 2222
          have p_delta_j: "delta (fst ?add_1_2) (snd ?add_1_2) x3 y3 \<noteq> 0 \<or> delta' (fst ?add_1_2) (snd ?add_1_2) x3 y3 \<noteq> 0"
            using 2222 unfolding e_aff_0_def e_aff_1_def by auto
          
          have "(?g1 \<oplus> ?g2) \<oplus> ?g3 = \<langle>proj_add ((x1, y1),0) ((x2, y2),0)\<rangle> \<oplus> ?g3"
            using assms independence_points p_delta_1_2(1) by auto  
          also have "... = \<langle>(proj_add (proj_add ((x1, y1),0) ((x2, y2),0)) ((x3, y3),0))\<rangle>"
            using assms independence_points p_delta_j
            by (metis (no_types, lifting) add_in_1_2 e_proj_aff prod.collapse proj_add'.simps) 
          also have "... = \<langle>(proj_add ((x1, y1),0) (proj_add  ((x2, y2),0) ((x3, y3),0)))\<rangle>"
            using assoc_points in_aff(1) in_aff(2) in_aff(3) p_delta_1_2(1) p_delta_2_3(1) p_delta_i p_delta_j by auto
          also have "... = ?g1 \<oplus> \<langle>proj_add' ((x2, y2),0) ((x3, y3),0)\<rangle>"
            by (metis (no_types, lifting) add_in_2_3 assms(1) e_proj_aff independence_points p_delta_2_3(1) p_delta_i prod.collapse proj_add'.simps)
          also have "... = ?g1 \<oplus> (?g2 \<oplus> ?g3)"
            by (simp add: assms(2) assms(3) independence_points)
          finally show ?thesis by blast      
        qed 
      qed
    qed
  qed
qed

lemma general_assoc:
  assumes "\<langle>((x1, y1), l)\<rangle> \<in> e_proj" "\<langle>((x2, y2), m)\<rangle> \<in> e_proj" "\<langle>((x3, y3), n)\<rangle> \<in> e_proj"
  shows "(\<langle>((x1, y1), l)\<rangle> \<oplus> \<langle>((x2, y2), m)\<rangle>) \<oplus> (\<langle>((x3, y3), n)\<rangle>) = \<langle>((x1, y1), l)\<rangle> \<oplus> (\<langle>((x2, y2), m)\<rangle> \<oplus> \<langle>((x3, y3), n)\<rangle>)"
proof -
  let ?t1 = "(\<langle>((x1, y1), 0)\<rangle> \<oplus> \<langle>((x2, y2), 0)\<rangle>) \<oplus> (\<langle>((x3, y3), 0)\<rangle>)" 
  let ?t2 = "\<langle>((x1, y1), 0)\<rangle> \<oplus> (\<langle>((x2, y2), 0)\<rangle> \<oplus> \<langle>((x3, y3), 0)\<rangle>)" 

  have e_proj_0: "\<langle>((x1, y1), 0)\<rangle> \<in> e_proj" "\<langle>((x2, y2), 0)\<rangle> \<in> e_proj" "\<langle>((x3, y3), 0)\<rangle> \<in> e_proj"
                 "\<langle>((x1, y1), 1)\<rangle> \<in> e_proj" "\<langle>((x2, y2), 1)\<rangle> \<in> e_proj" "\<langle>((x3, y3), 1)\<rangle> \<in> e_proj"
    using assms e_proj_aff by blast+
  have e_proj_add_0: "\<langle>((x1, y1), 0)\<rangle> \<oplus> \<langle>((x2, y2), 0)\<rangle> \<in> e_proj" 
                     "\<langle>((x2, y2), 0)\<rangle> \<oplus> \<langle>((x3, y3), 0)\<rangle> \<in> e_proj"
                     "\<langle>((x2, y2), 0)\<rangle> \<oplus> \<langle>((x3, y3), 1)\<rangle> \<in> e_proj"
                     "\<langle>((x1, y1), 0)\<rangle> \<oplus> \<langle>((x2, y2), 1)\<rangle> \<in> e_proj" 
                     "\<langle>((x2, y2), 1)\<rangle> \<oplus> \<langle>((x3, y3), 0)\<rangle> \<in> e_proj"
                     "\<langle>((x2, y2), 1)\<rangle> \<oplus> \<langle>((x3, y3), 1)\<rangle> \<in> e_proj" 
    using e_proj_0 well_defined proj_addition_def by blast+

  have eq3: "?t1 = ?t2"
    by(rewrite assoc_with_zeros,(simp add: e_proj_0)+)

  show ?thesis
    apply(cases "l"; cases "m"; cases "n")
    using tf_tau[of _ 0,simplified,symmetric] remove_add_tau' remove_add_tau
          e_proj_0 e_proj_add_0 by (simp add: eq3)+  
qed

lemma proj_assoc: 
  assumes "x \<in> e_proj" "y \<in> e_proj" "z \<in> e_proj" 
  shows "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
proof -
  obtain x1 y1 l x2 y2 m x3 y3 n where "x = \<langle>((x1, y1), l)\<rangle>" "y = \<langle>((x2, y2), m)\<rangle>" "z = \<langle>((x3, y3), n)\<rangle>"
    by (metis assms e_proj_def prod.collapse quotientE)
  then show ?thesis
    using assms general_assoc by force
qed

subsection \<open>Group law\<close>

lemma projective_group_law:
  shows "comm_group \<lparr>carrier = e_proj, mult = proj_addition, one = {((1,0),0)}\<rparr>" 
proof(unfold_locales,simp_all)
  show one_in: "{((1, 0), 0)} \<in> e_proj" using identity_proj by auto 

  show comm: "x \<oplus> y = y \<oplus> x" if "x \<in> e_proj" "y \<in> e_proj" for x y
    using proj_addition_comm that by simp
  
  show id_1: "{((1, 0), 0)} \<oplus> x = x" if "x \<in> e_proj" for x
    using proj_add_class_identity that by simp
  
  show id_2: "x \<oplus> {((1, 0), 0)} = x" if "x \<in> e_proj" for x
     using comm id_1 one_in that by simp

  show "e_proj \<subseteq> Units \<lparr>carrier = e_proj, mult = proj_addition, one = {((1, 0), 0)}\<rparr>"
    unfolding Units_def 
  proof(simp,standard)
    fix x
    assume "x \<in> e_proj"
    then obtain x' y' l' where "x = \<langle>((x',y'),l')\<rangle>"
      unfolding e_proj_def by(elim quotientE,auto)
    then have "\<langle>(i (x', y'), l')\<rangle> \<oplus> \<langle>((x',y'),l')\<rangle> = {((1, 0), 0)}" 
              "\<langle>((x',y'),l')\<rangle> \<oplus> \<langle>(i (x', y'), l')\<rangle> = {((1, 0), 0)}"
              "\<langle>(i (x', y'), l')\<rangle> \<in> e_proj"
      using proj_add_class_inv proj_addition_comm \<open>x \<in> e_proj\<close> by auto
    then show "x \<in> {y \<in> e_proj. \<exists>x\<in>e_proj. x \<oplus> y = {((1, 0), 0)} \<and> y \<oplus> x = {((1, 0), 0)}}"
      using \<open>x = \<langle>((x',y'),l')\<rangle>\<close> \<open>x \<in> e_proj\<close> by blast
  qed

  show "x \<oplus> y \<in> e_proj" if "x \<in> e_proj" "y \<in> e_proj" for x y
    using well_defined that by blast

  show "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"  if "x \<in> e_proj" "y \<in> e_proj" "z \<in> e_proj" for x y z
    using proj_assoc that by simp
qed

end

end




