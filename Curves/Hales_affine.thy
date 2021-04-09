theory Hales_affine
  imports  "HOL-Algebra.Group"  "HOL-Library.Bit" "HOL-Library.Rewrite"
begin

section\<open>Affine Edwards curves\<close>

class ell_field = field +
  assumes two_not_zero: "2 \<noteq> 0"

locale curve_addition =  
  fixes c d :: "'a::ell_field"
begin   

definition e :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "e x y = x^2 + c * y^2 - 1 - d * x^2 * y^2"

definition delta_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

definition delta_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

definition delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * 
                      (delta_minus x1 y1 x2 y2)"

lemma delta_com: 
  "(delta x0 y0 x1 y1 = 0) = (delta x1 y1 x0 y0 = 0)"
  unfolding delta_def delta_plus_def delta_minus_def 
  apply algebra
  done

fun add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - c*y1*y2) div (1-d*x1*y1*x2*y2), 
     (x1*y2+y1*x2) div (1+d*x1*y1*x2*y2))"

lemma commutativity: "add z1 z2 = add z2 z1"
  by(cases "z1",cases "z2",simp add: algebra_simps)

lemma add_closure: 
  assumes "z3 = (x3,y3)" "z3 = add (x1,y1) (x2,y2)"
  assumes "delta_minus x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0"
  assumes "e x1 y1 = 0" "e x2 y2 = 0" 
  shows "e x3 y3 = 0" 
proof -
  have x3_expr: "x3 = (x1*x2 - c*y1*y2) div (delta_minus x1 y1 x2 y2)"
    using assms delta_minus_def by auto
  have y3_expr: "y3 = (x1*y2+y1*x2) div (delta_plus x1 y1 x2 y2)"
    using assms delta_plus_def by auto

  have "\<exists> r1 r2. (e x3 y3)*(delta x1 y1 x2 y2)\<^sup>2 - (r1 * e x1 y1 + r2 * e x2 y2) = 0"
    unfolding e_def x3_expr y3_expr delta_def
    apply(simp add: divide_simps assms)    
    unfolding delta_plus_def delta_minus_def 
    by algebra
  then show "e x3 y3 = 0" 
    using assms 
    by (simp add: delta_def)
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

  then have "gxpoly = 0" 
    using e1_def assms(13-15) e2_def e3_def by auto
  have "Delta\<^sub>x \<noteq> 0" 
    using Delta\<^sub>x_def delta_def assms(7-11) non_unfolded_adds by auto
  then have "g\<^sub>x = 0" 
    using \<open>gxpoly = 0\<close> gxpoly_def by auto

  have simp1gy: "(x1' * y3 + y1' * x3) * delta_plus x1 y1 x3' y3' * (delta x1 y1 x2 y2 * delta x2 y2 x3 y3) = 
     ((x1 * x2 - c * y1 * y2) * y3 * delta_plus x1 y1 x2 y2 + (x1 * y2 + y1 * x2) * x3 * delta_minus x1 y1 x2 y2) *
    (delta_minus x2 y2 x3 y3 * delta_plus x2 y2 x3 y3 + d * x1 * y1 * (x2 * x3 - c * y2 * y3) * (x2 * y3 + y2 * x3))"
    apply(rewrite x1'_expr y1'_expr x3'_expr y3'_expr)+
    apply(rewrite delta_plus_def) 
    apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric] delta_plus_def[symmetric])+
    unfolding delta_def
    by(simp add: divide_simps assms(5-8))
    
  have simp2gy: "(x1 * y3' + y1 * x3') * delta_plus x1' y1' x3 y3 * (delta x1 y1 x2 y2 * delta x2 y2 x3 y3) = 
     (x1 * (x2 * y3 + y2 * x3) * delta_minus x2 y2 x3 y3 + y1 * (x2 * x3 - c * y2 * y3) * delta_plus x2 y2 x3 y3) *
    (delta_minus x1 y1 x2 y2 * delta_plus x1 y1 x2 y2 + d * (x1 * x2 - c * y1 * y2) * (x1 * y2 + y1 * x2) * x3 * y3)"
    apply(rewrite x1'_expr y1'_expr x3'_expr y3'_expr)+
    apply(rewrite delta_plus_def)
    apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric] delta_plus_def[symmetric])+
    unfolding delta_def
    by(simp add: divide_simps assms(5-8))

  have "\<exists> r1 r2 r3. gypoly = r1 * e1 + r2 * e2 + r3 * e3"
    unfolding gypoly_def g\<^sub>y_def Delta\<^sub>y_def 
    apply(simp add: assms(1,2))
    apply(rewrite in "_ / \<hole>" delta_plus_def[symmetric])+
    apply(simp add: divide_simps assms(10,12))
    apply(rewrite left_diff_distrib)
    apply(simp add: simp1gy simp2gy)
    unfolding delta_plus_def delta_minus_def
              e1_def e2_def e3_def e_def 
    by algebra

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
  using assms 
  apply(simp add: delta_plus_def e_def) 
  by algebra
  
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
  {
    assume "(1 - d*y1^2*x2^2) = 0"
    then have "1/d = y1^2*x2^2" "1/d \<noteq> 0"     
      apply(auto simp add: divide_simps \<open>d \<noteq> 0\<close>) 
      by algebra
  }
  note case1 = this
  {assume "(1 - c*d*y1^2*y2^2) = 0" "(1 - d*y1^2*x2^2) \<noteq> 0"
    then have "c \<noteq> 0" by auto
    then have "1/(c*d) = y1^2*y2^2" "1/(c*d) \<noteq> 0" 
      apply(simp add: divide_simps \<open>d \<noteq> 0\<close> \<open>c \<noteq> 0\<close>) 
      using \<open>(1 - c*d*y1^2*y2^2) = 0\<close> apply algebra
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
 (is "comm_group ?g")
proof(unfold_locales)
  {fix x1 y1 x2 y2
  assume "e x1 y1 = 0" "e x2 y2 = 0"
  have "e (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) = 0"
    apply(simp)
    using add_closure delta_non_zero[OF \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close> assms(1) assms(2)] 
          delta_def \<open>e x1 y1 = 0\<close> \<open>e x2 y2 = 0\<close> by auto}
  then show "
      \<And>x y. x \<in> carrier ?g \<Longrightarrow> y \<in> carrier ?g \<Longrightarrow>
           x \<otimes>\<^bsub>?g\<^esub> y \<in> carrier ?g" by auto
next
  {fix x1 y1 x2 y2 x3 y3 
   assume "e x1 y1 = 0" "e x2 y2 = 0" "e x3 y3 = 0" 
   then have "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
     using assms(1,2) delta_non_zero by blast+
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
       x \<in> carrier ?g \<Longrightarrow> y \<in> carrier ?g \<Longrightarrow> z \<in> carrier ?g \<Longrightarrow>
       x \<otimes>\<^bsub>?g\<^esub> y \<otimes>\<^bsub>?g\<^esub> z = x \<otimes>\<^bsub>?g\<^esub> (y \<otimes>\<^bsub>?g\<^esub> z)" by auto
next
  show "\<one>\<^bsub>?g\<^esub> \<in> carrier ?g" by (simp add: e_def)
next
  show "\<And>x. x \<in> carrier ?g \<Longrightarrow> \<one>\<^bsub>?g\<^esub> \<otimes>\<^bsub>?g\<^esub> x = x"
    by (simp add: commutativity neutral)
next
  show "\<And>x. x \<in> carrier ?g \<Longrightarrow> x \<otimes>\<^bsub>?g\<^esub> \<one>\<^bsub>?g\<^esub> = x"
    by (simp add: neutral)
next
  show "\<And>x y. x \<in> carrier ?g \<Longrightarrow> y \<in> carrier ?g \<Longrightarrow>
           x \<otimes>\<^bsub>?g\<^esub> y = y \<otimes>\<^bsub>?g\<^esub> x"
    using commutativity by auto
next
  show "carrier ?g \<subseteq> Units ?g"
  proof(simp,standard)
    fix z
    assume "z \<in> {(x, y). local.e x y = 0}"
    show "z \<in> Units ?g" 
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
end