theory Hales
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
text_raw \<open>
\begin{figure}
\begin{center}\begin{minipage}{0.6\textwidth}
\isastyleminor\isamarkuptrue
\<close>
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

section\<open>Extension\<close>
(* Generalize for c \<noteq> 1 *)
locale ext_curve_addition = curve_addition +
  fixes t' :: "'a::ell_field"
  assumes c_eq_1: "c = 1"
  assumes t_intro: "d = t'^2"
  assumes t_ineq: "t'^2 \<noteq> 1" "t' \<noteq> 0"
begin

subsection \<open>Change of variables\<close>
(*lemma c_d_pos: "d \<ge> 0" 
  using t_intro by auto

lemma delta_plus_self: "delta_plus x0 y0 x0 y0 \<noteq> 0" 
  unfolding delta_plus_def
        apply (simp add: semiring_normalization_rules(18) semiring_normalization_rules(29) two_not_zero)  

    apply(subst (1) mult.assoc,subst (2) mult.assoc,subst (1) mult.assoc)
    apply(subst power2_eq_square[symmetric])
    using t_intro t_ineq
    using mult_nonneg_nonneg[OF _ zero_le_power2[of "x0*y0"]] by simp
*)
(* TODO: defomotopm so that rewriting leaves t' inside of the terms *)
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
    using t_nm1 t_def by argo
qed

subsection \<open>New points\<close>

definition e' where "e' x y = x^2 + y^2 - 1 - t^2 * x^2 * y^2"

definition "e'_aff = {(x,y). e' x y = 0}" 
  definition "e_circ = {(x,y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> (x,y) \<in> e'_aff}"

lemma e_e'_iff: "e x y = 0 \<longleftrightarrow> e' x y = 0"
  unfolding e_def e'_def using c_eq_1 t_expr(1) t_def by simp

lemma circ_to_aff: "p \<in> e_circ \<Longrightarrow> p \<in> e'_aff"
  unfolding e_circ_def by auto

text\<open>The case \<^text>\<open>t^2 = 1\<close> corresponds to a product of intersecting lines 
     which cannot be a group\<close>

lemma t_2_1_lines:
  "t^2 = 1 \<Longrightarrow> e' x y = - (1 - x^2) * (1 - y^2)" 
  unfolding e'_def by algebra

text\<open>The case \<^text>\<open>t = 0\<close> corresponds to a circle which has been treated before\<close>

lemma t_0_circle:
  "t = 0 \<Longrightarrow> e' x y = x^2 + y^2 - 1" 
  unfolding e'_def by auto

subsection \<open>Group transformations and inversions\<close>

(*
  TODO: 
  Obtain theorems as a conclusion that G is a group 
  Watch for duplication of facts
*)

fun \<rho> :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where 
  "\<rho> (x,y) = (-y,x)"
fun \<tau> :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where 
  "\<tau> (x,y) = (1/(t*x),1/(t*y))"

definition G where
  "G \<equiv> {id,\<rho>,\<rho> \<circ> \<rho>,\<rho> \<circ> \<rho> \<circ> \<rho>,\<tau>,\<tau> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>}"

definition symmetries where 
  "symmetries = {\<tau>,\<tau> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho>,\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>}"

definition rotations where
  "rotations = {id,\<rho>,\<rho> \<circ> \<rho>,\<rho> \<circ> \<rho> \<circ> \<rho>}"

lemma G_partition: "G = rotations \<union> symmetries"
  unfolding G_def rotations_def symmetries_def by fastforce

(* See if we can remove this and leave only tau_idemps *)
lemma tau_sq: "(\<tau> \<circ> \<tau>) (x,y) = (x,y)" by(simp add: t_nz)

lemma tau_idemp: "\<tau> \<circ> \<tau> = id"
  using t_nz comp_def by auto 

lemma tau_idemp_explicit: "\<tau>(\<tau>(x,y)) = (x,y)"
  using tau_idemp pointfree_idE by fast

lemma tau_idemp_point: "\<tau>(\<tau> p) = p"
  using o_apply[symmetric, of \<tau> \<tau> p] tau_idemp by simp  

fun i :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where 
  "i (a,b) = (a,-b)" 

lemma i_idemp: "i \<circ> i = id"
  using comp_def by auto

lemma i_idemp_explicit: "i(i(x,y)) = (x,y)"
  using i_idemp pointfree_idE by fast

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
  shows "\<exists> tr' \<in> rotations. (tr \<circ> i) (x,y) = (i \<circ> tr') (x,y) \<and> tr \<circ> tr' = id"
  using assms rho_i_com_inverses unfolding rotations_def by fastforce

lemma tau_i_com_inverses:
  "(i \<circ> \<tau>) (x,y) = (\<tau> \<circ> i) (x,y)"
  "(i \<circ> \<tau> \<circ> \<rho>) (x,y) = (\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) (x,y)"
  "(i \<circ> \<tau> \<circ> \<rho> \<circ> \<rho>) (x,y) = (\<tau> \<circ> \<rho> \<circ> \<rho> \<circ> i) (x,y)"
  "(i \<circ> \<tau> \<circ> \<rho> \<circ> \<rho> \<circ> \<rho>) (x,y) = (\<tau> \<circ> \<rho> \<circ> i) (x,y)"
  by(simp)+

lemma rho_circ: 
  assumes "p \<in> e_circ"
  shows "\<rho> p \<in> e_circ"
  using assms unfolding e_circ_def e'_aff_def e'_def 
  by(simp split: prod.splits add: add.commute)

lemma i_aff:
  assumes "p \<in> e'_aff"
  shows "i p \<in> e'_aff"
  using assms unfolding e'_aff_def e'_def by auto

lemma i_circ:
  assumes "(x,y) \<in> e_circ"
  shows "i (x,y) \<in> e_circ"
  using assms unfolding e_circ_def e'_aff_def e'_def by auto

lemma i_circ_points:
  assumes "p \<in> e_circ"
  shows "i p \<in> e_circ"
  using assms unfolding e_circ_def e'_aff_def e'_def by auto

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
  unfolding e'_aff_def e'_def
  apply(simp split: prod.splits) 
  apply(simp add: divide_simps t_nz)
  apply(subst power_mult_distrib)+
  apply(subst ring_distribs(1)[symmetric])+
  apply(subst (1) mult.assoc)
  apply(subst right_diff_distrib[symmetric])
  apply(simp add: t_nz)
  by(simp add: algebra_simps)


lemma rot_comp:
  assumes "t1 \<in> rotations" "t2 \<in> rotations"
  shows "t1 \<circ> t2 \<in> rotations"
  using assms unfolding rotations_def by auto


lemma rot_tau_com:
  assumes "tr \<in> rotations"
  shows "tr \<circ> \<tau> = \<tau> \<circ> tr"
  using assms unfolding rotations_def by(auto)

lemma tau_i_com:
  "\<tau> \<circ> i = i \<circ> \<tau>" by auto

lemma rot_com:
  assumes "r \<in> rotations" "r' \<in> rotations"
  shows "r' \<circ> r = r \<circ> r'" 
  using assms unfolding rotations_def by force

lemma rot_inv:
  assumes "r \<in> rotations"
  shows "\<exists> r' \<in> rotations. r' \<circ> r = id" 
  using assms unfolding rotations_def by force

lemma rot_aff:
  assumes "r \<in> rotations" "p \<in> e'_aff"
  shows "r p \<in> e'_aff"
  using assms unfolding rotations_def e'_aff_def e'_def
  by(auto simp add: semiring_normalization_rules(16) add.commute)

(* Can be erased *) 
lemma rot_delta:
  assumes "r \<in> rotations" "delta x1 y1 x2 y2 \<noteq> 0"
  shows "delta (fst (r (x1,y1))) (snd (r (x1,y1))) x2 y2 \<noteq> 0"
  using assms unfolding rotations_def delta_def delta_plus_def delta_minus_def
  apply(safe)
  apply simp 
  apply (simp add: semiring_normalization_rules(16))
  apply(simp) 
  by(simp add: add_eq_0_iff equation_minus_iff semiring_normalization_rules(16))

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
   apply (metis c_eq_1 mult_numeral_1 numeral_One one_neq_zero 
                power2_minus power_one t_sq_n1)
  by (metis d_nz)

lemma sym_decomp:
  assumes "g \<in> symmetries"
  shows "\<exists> r \<in> rotations. g = \<tau> \<circ> r"
  using assms unfolding symmetries_def rotations_def by auto

(* TODO: not used, remove *)
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

fun ext_add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
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

definition e'_aff_0 where
  "e'_aff_0 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e'_aff \<and> 
                                 (x2,y2) \<in> e'_aff \<and> 
                                 delta x1 y1 x2 y2 \<noteq> 0 }"

definition e'_aff_1 where
  "e'_aff_1 = {((x1,y1),(x2,y2)). (x1,y1) \<in> e'_aff \<and> 
                                 (x2,y2) \<in> e'_aff \<and> 
                                 delta' x1 y1 x2 y2 \<noteq> 0 }"

lemma ext_add_comm:
  "ext_add (x1,y1) (x2,y2) = ext_add (x2,y2) (x1,y1)"
  by(simp add: divide_simps,algebra) 

lemma ext_add_comm_points:
  "ext_add z1 z2 = ext_add z2 z1"
  using ext_add_comm 
  apply(subst (1 3 4 6) surjective_pairing)
  by presburger

lemma ext_add_inverse:
  "x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> ext_add (x,y) (i (x,y)) = (1,0)"
  by(simp add: two_not_zero)

lemma ext_add_deltas:
  "ext_add (x1,y1) (x2,y2) =
    ((delta_x x2 y1 x1 y2) div (delta_x x1 y1 x2 y2),
     (delta_y x1 x2 y1 y2) div (delta_y x1 y1 x2 y2))"
  unfolding delta_x_def delta_y_def by simp 

subsubsection \<open>Inversion and rotation invariance\<close>

lemma inversion_invariance_1:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  shows "add (\<tau> (x1,y1)) (x2,y2) = add (x1,y1) (\<tau> (x2,y2))"
  apply(simp)
  apply(subst c_eq_1)+
  apply(simp add: algebra_simps)
  apply(subst power2_eq_square[symmetric])+
  apply(subst t_expr)+
  apply(rule conjI)
  apply(simp_all add: divide_simps assms t_nz d_nz)
  by(simp_all add: algebra_simps)



lemma inversion_invariance_2:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  shows "ext_add (\<tau> (x1,y1)) (x2,y2) = ext_add (x1,y1) (\<tau> (x2,y2))"
  apply(simp add: divide_simps t_nz assms) 
  by algebra

lemma rho_invariance_1: 
  "add (\<rho> (x1,y1)) (x2,y2) = \<rho> (add (x1,y1) (x2,y2))"
  apply(simp)
  apply(subst c_eq_1)+
  by(simp add: algebra_simps divide_simps)

(* TODO: this form is more convenient for proving later on *)
lemma rho_invariance_1_points:
  "add (\<rho> p1) p2 = \<rho> (add p1 p2)"
  using rho_invariance_1 
  apply(subst (2 4 6 8) surjective_pairing)
  by blast

lemma rotation_invariance_1: 
  assumes "r \<in> rotations"
  shows "add (r (x1,y1)) (x2,y2) = r (add (x1,y1) (x2,y2))"
  using rho_invariance_1_points assms unfolding rotations_def
  apply(safe)
  apply(simp,simp) 
  by(metis comp_apply prod.exhaust_sel)+

lemma rotation_invariance_1_points: 
  assumes "r \<in> rotations"
  shows "add (r p1) p2 = r (add p1 p2)"
  using rotation_invariance_1 assms 
  unfolding rotations_def
  apply(safe)
  apply(simp,simp) 
  using rho_invariance_1_points by auto

lemma rho_invariance_2: 
  "ext_add (\<rho> (x1,y1)) (x2,y2) = 
   \<rho> (ext_add (x1,y1) (x2,y2))"
  by(simp add: algebra_simps divide_simps)

lemma rho_invariance_2_points:
  "ext_add (\<rho> p1) p2 = \<rho> (ext_add p1 p2)"
  using rho_invariance_2
  apply(subst (2 4 6 8) surjective_pairing)
  by blast

lemma rotation_invariance_2: 
  assumes "r \<in> rotations"
  shows "ext_add (r (x1,y1)) (x2,y2) = r (ext_add (x1,y1) (x2,y2))"
  using rho_invariance_2_points assms unfolding rotations_def
  apply(safe)
  apply(simp,simp) 
  by(metis comp_apply prod.exhaust_sel)+

lemma rotation_invariance_2_points: 
  assumes "r \<in> rotations"
  shows "ext_add (r p1) p2 = r (ext_add p1 p2)"
  using rotation_invariance_2 assms 
  unfolding rotations_def
  apply(safe)
  apply(simp,simp) 
  using rho_invariance_2_points by auto

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
  "i (add (x1,y1) (x2,y2)) = add (i (x1,y1)) (i (x2,y2))"
  by(simp add: divide_simps)
lemma inverse_rule_4:
  "i (ext_add (x1,y1) (x2,y2)) = ext_add (i (x1,y1)) (i (x2,y2))"
  by(simp add: algebra_simps divide_simps)

(* This kind of lemma may vary with different fields *)
lemma e'_aff_x0:
  assumes "x = 0" "(x,y) \<in> e'_aff"
  shows "y = 1 \<or> y = -1"
  using assms unfolding e'_aff_def e'_def
  by(simp,algebra)

lemma e'_aff_y0:
  assumes "y = 0" "(x,y) \<in> e'_aff"
  shows "x = 1 \<or> x = -1"
  using assms unfolding e'_aff_def e'_def
  by(simp,algebra) 


(* 
 TODO: note that this proof does not go through in the general case (as written in the paper)
  thus, dichotomy will have to rule out some cases.
*)
lemma add_ext_add:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" 
  shows "ext_add (x1,y1) (x2,y2) = \<tau> (add (\<tau> (x1,y1)) (x2,y2))"
  apply(simp)
  apply(rule conjI)
  apply(simp add: c_eq_1)
  apply(simp add: divide_simps t_nz power2_eq_square[symmetric] assms t_expr(1) d_nz)
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1)) 
  apply (simp add: semiring_normalization_rules(18) semiring_normalization_rules(29) t_intro)
  apply(simp add: divide_simps t_nz power2_eq_square[symmetric] assms t_expr(1) d_nz)
  apply(simp add: algebra_simps power2_eq_square[symmetric] t_expr(1))  
  by (simp add: power2_eq_square t_intro)

corollary add_ext_add_2:
  assumes "x1 \<noteq> 0" "y1 \<noteq> 0" 
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
    using add_ext_add[OF p_nz] tau_idemp by simp
  also have "... = \<tau> (ext_add (\<tau> (x1, y1)) (x2, y2))"
    using tau_expr tau_idemp by auto
  finally show ?thesis by blast
qed

subsubsection \<open>Coherence and closure\<close>

lemma coherence_1:
  assumes "delta_x x1 y1 x2 y2 \<noteq> 0" "delta_minus x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "delta_x x1 y1 x2 y2 * delta_minus x1 y1 x2 y2 *
         (fst (ext_add (x1,y1) (x2,y2)) - fst (add (x1,y1) (x2,y2)))
         = x2 * y2 * e' x1 y1 - x1 * y1 * e' x2 y2"
  apply(simp)  
  apply(rewrite in "_ / \<hole>" delta_x_def[symmetric])
  apply(rewrite in "_ / \<hole>" delta_minus_def[symmetric])
  apply(simp add: c_eq_1 assms(1,2) divide_simps)
  unfolding delta_minus_def delta_x_def e'_def
  apply(simp add: t_expr)
  by(simp add: power2_eq_square field_simps)  
  
lemma coherence_2:
  assumes "delta_y x1 y1 x2 y2 \<noteq> 0" "delta_plus x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "delta_y x1 y1 x2 y2 * delta_plus x1 y1 x2 y2 *
         (snd (ext_add (x1,y1) (x2,y2)) - snd (add (x1,y1) (x2,y2)))
         = - x2 * y2 * e' x1 y1 - x1 * y1 * e' x2 y2"
  apply(simp)  
  apply(rewrite in "_ / \<hole>" delta_y_def[symmetric])
  apply(rewrite in "_ / \<hole>" delta_plus_def[symmetric])
  apply(simp add: c_eq_1 assms(1,2) divide_simps)
  unfolding delta_plus_def delta_y_def e'_def
  apply(subst t_expr)+
  by(simp add: power2_eq_square  field_simps)
  
lemma coherence:
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0"
  shows "ext_add (x1,y1) (x2,y2) = add (x1,y1) (x2,y2)"
  using coherence_1 coherence_2 delta_def delta'_def assms by auto

lemma ext_add_closure:
  assumes "delta' x1 y1 x2 y2 \<noteq> 0"
  assumes "e' x1 y1 = 0" "e' x2 y2 = 0" 
  assumes "(x3,y3) = ext_add (x1,y1) (x2,y2)"
  shows "e' x3 y3 = 0"
proof -
  have deltas_nz: "delta_x x1 y1 x2 y2 \<noteq> 0"
                  "delta_y x1 y1 x2 y2 \<noteq> 0"
    using assms(1) delta'_def by auto

  have v3: "x3 = fst (ext_add (x1,y1) (x2,y2))"
           "y3 = snd (ext_add (x1,y1) (x2,y2))"
    using assms(4) by simp+

  have "\<exists> a b. t^4 * (delta_x x1 y1 x2 y2)^2 * (delta_y x1 y1 x2 y2)^2 * e' x3 y3 = 
               a * e' x1 y1 + b * e' x2 y2"
    using deltas_nz
    unfolding e'_def v3 delta_x_def delta_y_def
    apply(simp add: divide_simps) 
    by algebra

  then show "e' x3 y3 = 0"
    using assms(2,3) deltas_nz t_nz by auto  
qed

lemma ext_add_closure_points:
  assumes "delta' x1 y1 x2 y2 \<noteq> 0"
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" 
  shows "ext_add (x1,y1) (x2,y2) \<in> e'_aff"
  using ext_add_closure assms 
  unfolding e'_aff_def by auto

subsubsection \<open>Useful lemmas in the extension\<close>

lemma inverse_generalized:
  assumes "(a,b) \<in> e'_aff" "delta_plus a b a b \<noteq> 0"
  shows "add (a,b) (a,-b) = (1,0)" 
  using inverse assms
  unfolding e'_aff_def
  using e_e'_iff 
  by(simp) 

lemma add_closure_points:
  assumes "delta x y x' y' \<noteq> 0"
          "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff"
  shows "add (x,y) (x',y') \<in> e'_aff"
  using add_closure assms e_e'_iff
  unfolding delta_def e'_aff_def by auto

lemma add_self:
  assumes in_aff: "(x,y) \<in> e'_aff"
  shows "delta x y x (-y) \<noteq> 0 \<or> delta' x y x (-y) \<noteq> 0 "
    using in_aff d_n1 
    unfolding delta_def delta_plus_def delta_minus_def
              delta'_def delta_x_def delta_y_def
              e'_aff_def e'_def
    apply(simp add: t_expr two_not_zero)
    apply(safe)
    apply(simp_all add: algebra_simps) 
    by(simp add: semiring_normalization_rules(18) semiring_normalization_rules(29) two_not_zero)+

subsection \<open>Delta arithmetic\<close>

lemma mix_tau:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "x2 \<noteq> 0" "y2 \<noteq> 0"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e'_aff_def e'_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_nz algebra_simps)
  apply(simp add: power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz)
  by algebra

lemma mix_tau_0:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "x2 \<noteq> 0" "y2 \<noteq> 0"
  assumes "delta x1 y1 x2 y2 = 0"
  shows "delta' x1 y1 x2 y2 = 0 \<or> delta' x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) = 0" 
  using assms
  unfolding e'_aff_def e'_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_nz algebra_simps)
  apply(simp add: power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps t_nz)
  by algebra

lemma mix_tau_prime:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "x2 \<noteq> 0" "y2 \<noteq> 0"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x1 y1 (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta' x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e'_aff_def e'_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_nz algebra_simps)
  apply(simp add: power2_eq_square[symmetric] t_expr d_nz)
  apply(simp add: divide_simps)
  by algebra

lemma tau_tau_d:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" 
  assumes "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e'_aff_def e'_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_expr)
  apply(simp split: if_splits add: divide_simps t_nz)
  apply(simp_all add: t_nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply algebra
  by algebra

lemma tau_tau_d':
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" 
  assumes "delta' (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) (fst (\<tau> (x2,y2))) (snd (\<tau> (x2,y2))) \<noteq> 0" 
  shows "delta' x1 y1 x2 y2 \<noteq> 0"
  using assms
  unfolding e'_aff_def e'_def delta_def delta_plus_def delta_minus_def delta'_def delta_y_def delta_x_def
  apply(simp)
  apply(simp add: t_expr)
  apply(simp split: if_splits add: divide_simps t_nz) 
  apply fastforce
  apply algebra
  by algebra

lemma delta_add_delta'_1: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes r_expr: "rx = fst (add (x1,y1) (x2,y2))" "ry = snd (add (x1,y1) (x2,y2))" 
  assumes in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff"
  assumes pd: "delta x1 y1 x2 y2 \<noteq> 0" 
  assumes pd': "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  using pd in_aff unfolding r_expr delta_def delta_minus_def delta_plus_def
                            e'_aff_def e'_def
  apply(simp add: divide_simps t_expr)
  apply(simp add: c_eq_1 algebra_simps)
  by algebra

lemma delta'_add_delta_1: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes r_expr: "rx = fst (ext_add (x1,y1) (x2,y2))" "ry = snd (ext_add (x1,y1) (x2,y2))" 
  assumes in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff"
  assumes pd': "delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  using in_aff unfolding r_expr delta_def delta_minus_def delta_plus_def
                            e'_aff_def e'_def
  apply(simp split: if_splits add: divide_simps t_expr)
  apply(simp add: c_eq_1 algebra_simps)
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
  assumes in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff"
  assumes pd: "delta x1 y1 x2 y2 \<noteq> 0" 
  assumes pd': "delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0" 
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply safe
  using pd unfolding r_expr delta_def delta_minus_def delta_plus_def
  apply(simp)
  apply(simp add: c_eq_1 divide_simps)
  using in_aff unfolding e'_aff_def e'_def
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
  assumes in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff"
  assumes pd: "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes pd': "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
  shows "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
  using pd' unfolding delta_def delta_minus_def delta_plus_def
                      delta'_def delta_x_def delta_y_def 
  apply(simp split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  apply safe
  using pd unfolding r_expr delta'_def delta_x_def delta_y_def
  apply(simp)
  apply(simp split: if_splits add: c_eq_1 divide_simps)
  using in_aff unfolding e'_aff_def e'_def
  apply(simp add: t_expr)
  apply safe  
  using funny_field_lemma_2 by fast

lemma delta'_add_delta_not_add: 
  assumes 1: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
  assumes in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff"
  assumes pd: "delta' x1 y1 x2 y2 \<noteq> 0" 
  assumes add_nz: "fst (ext_add (x1,y1) (x2,y2)) \<noteq> 0"  "snd (ext_add (x1,y1) (x2,y2)) \<noteq> 0"
  shows pd': "delta (fst (\<tau> (x1,y1))) (snd (\<tau> (x1,y1))) x2 y2 \<noteq> 0"
  using add_ext_add[OF ] 1 in_aff
  using pd 1  unfolding delta_def delta_minus_def delta_plus_def
                        delta'_def delta_x_def delta_y_def 
                     e'_aff_def e'_def
  apply(simp add: divide_simps t_nz)
  apply(simp_all add: c_eq_1) 
   apply(simp_all split: if_splits add: divide_simps t_nz 1 algebra_simps power2_eq_square[symmetric] t_expr d_nz)
  using add_nz
  apply(simp add: d_nz) 
  using d_nz 
  by (metis distrib_left mult_eq_0_iff)

lemma not_add_self:
  assumes in_aff: "(x,y) \<in> e'_aff" "x \<noteq> 0" "y \<noteq> 0" 
  shows "delta x y (fst (\<tau> (i (x,y)))) (snd (\<tau> (i (x,y)))) = 0"
        "delta' x y (fst (\<tau> (i (x,y)))) (snd (\<tau> (i (x,y)))) = 0"
    using in_aff d_n1 
    unfolding delta_def delta_plus_def delta_minus_def
              delta'_def delta_x_def delta_y_def
              e'_aff_def e'_def
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
    then have "e' x y = 2 * (1 - t) / t \<or> e' x y = 2 * (-1 - t) / t"
      using nz t_nz unfolding e'_def 
      by(simp add: algebra_simps divide_simps,algebra)
    then have "e' x y \<noteq> 0" 
      using t_dneq2 t_n1
      by(auto simp add: algebra_simps divide_simps t_nz) 
    then have "False"
      using assms nz p_def unfolding e_circ_def e'_aff_def by fastforce
    then show ?thesis by simp
  qed
qed

lemma dichotomy_1:
  assumes "p \<in> e'_aff" "q \<in> e'_aff" 
  shows "(p \<in> e_circ \<and> (\<exists> g \<in> symmetries. q = (g \<circ> i) p)) \<or> 
         (p,q) \<in> e'_aff_0 \<or> (p,q) \<in> e'_aff_1" 
proof -
  obtain x1 y1 where p_def: "p = (x1,y1)" by fastforce
  obtain x2 y2 where q_def: "q = (x2,y2)" by fastforce
  
  consider (1) "(p,q) \<in> e'_aff_0" |
           (2) "(p,q) \<in> e'_aff_1" |
           (3) "(p,q) \<notin> e'_aff_0 \<and> (p,q) \<notin> e'_aff_1" by blast
  then show ?thesis
  proof(cases)
    case 1 then show ?thesis by blast  
  next
    case 2 then show ?thesis by simp
  next
    case 3
    then have "delta x1 y1 x2 y2 = 0" "delta' x1 y1 x2 y2 = 0"
      unfolding p_def q_def e'_aff_0_def e'_aff_1_def using assms 
      by (simp add: assms p_def q_def)+
    have "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
      using \<open>delta x1 y1 x2 y2 = 0\<close> 
      unfolding delta_def delta_plus_def delta_minus_def by auto
    then have "p \<in> e_circ" "q \<in> e_circ"
      unfolding e_circ_def using assms p_def q_def by blast+
    
    obtain a0 b0 where tq_expr: "\<tau> q = (a0,b0)" by fastforce
    then have q_expr: "q = \<tau> (a0,b0)" using tau_idemp_explicit q_def by auto
    obtain a1 b1 where p_expr: "p = (a1,b1)" by fastforce
    have a0_nz: "a0 \<noteq> 0" "b0 \<noteq> 0"
      using \<open>\<tau> q = (a0, b0)\<close> \<open>x2 \<noteq> 0\<close> \<open>y2 \<noteq> 0\<close> comp_apply q_def tau_sq by auto

    have a1_nz: "a1 \<noteq> 0" "b1 \<noteq> 0"
      using \<open>p = (a1, b1)\<close> \<open>x1 \<noteq> 0\<close> \<open>y1 \<noteq> 0\<close> p_def by auto

    have in_aff: "(a0,b0) \<in> e'_aff" "(a1,b1) \<in> e'_aff"
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

    have "(\<exists> g \<in> symmetries. q = (g \<circ> i) p)"
    proof(cases "delta_minus a1 b1 (fst q) (snd q) = 0")
      case True
      then have t1: "delta_minus a1 b1 (fst q) (snd q) = 0" 
        using \<open>delta x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> delta_def p_def q_def by auto
      then show ?thesis 
      proof(cases "\<delta>_plus a0 b0 = 0")
        case True
        then have cas1: "delta_minus a1 b1 (fst q) (snd q) = 0"
                        "\<delta>_plus a0 b0 = 0" 
          using t1 by auto
        have \<delta>'_expr: "\<delta>' a0 b0 = a0*b0 - a1*b1"
         unfolding \<delta>'_def delta_minus_def 
         by(simp add: algebra_simps a0_nz a1_nz power2_eq_square[symmetric] t_expr d_nz)

        have eq1': "a0*b0 - a1*b1 = 0" 
          using \<delta>'_expr q_def tau_sq tq_expr cas1(1) unfolding \<delta>'_def by fastforce
        then have eq1: "a0 = a1 * (b1 / b0)"  
          using a0_nz(2) by(simp add: divide_simps) 
    
        have eq2: "b0^2 - a1^2 = 0"
          using cas1(2) unfolding \<delta>_plus_def delta_x_def 
          by(simp add: divide_simps a0_nz a1_nz t_nz eq1 power2_eq_square[symmetric])
        
        have eq3: "a0^2 - b1^2 = 0"
          using eq1 eq2 
          by(simp add: divide_simps a0_nz a1_nz eq1 eq2 power2_eq_square right_diff_distrib')
    
        have "(a0,b0) = (b1,a1) \<or> (a0,b0) = (-b1,-a1)" 
          using eq2 eq3 eq1' by algebra        
        then have "(a0,b0) \<in> {(b1,a1),(-b1,-a1)}" by simp
        moreover have "{(b1,a1),(-b1,-a1)} \<subseteq> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
          using \<open>p = (a1, b1)\<close> by auto
        ultimately have "\<exists> g \<in> rotations. \<tau> q = (g \<circ> i) p"
          unfolding rotations_def by (auto simp add: \<open>\<tau> q = (a0, b0)\<close>)

        then obtain g where "g \<in> rotations" "\<tau> q = (g \<circ> i) p" by blast
        then have "q = (\<tau> \<circ> g \<circ> i) p"
          using tau_sq \<open>\<tau> q = (a0, b0)\<close> q_def by auto
        then show ?thesis
          using tau_rot_sym \<open>g \<in> rotations\<close> symmetries_def by blast     
    next
      case False
        (* in this case we need to use the in_aff equations *)
        then have cas2: "delta_minus a1 b1 (fst q) (snd q) = 0"
                        "\<delta>_minus a0 b0 = 0"               
          using t1 \<delta>_minus_def \<delta>_plus_def \<open>delta' x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> 
                delta'_def 3 q_def p_def tq_expr by auto
        
        have \<delta>'_expr: "\<delta>' a0 b0 = a0*b0 - a1*b1"
          unfolding \<delta>'_def delta_minus_def 
          by(simp add: algebra_simps a0_nz a1_nz power2_eq_square[symmetric] t_expr d_nz)

        have eq1: "a1 * b0 + b1 * a0  = 0"
          using cas2(2) unfolding \<delta>_minus_def delta_y_def 
          by(simp add: divide_simps a0_nz a1_nz t_nz power2_eq_square[symmetric])
         
        have eq2: "a0*b0 - a1*b1 = 0"
          using \<delta>'_expr q_def tau_sq tq_expr cas2(1) unfolding \<delta>'_def by fastforce

        define c1 where "c1 = a0^2*b0^2" 
        define c2 where "c2 = a1^2*b0^2"
        have c_eqs: "c1 = a0^2*b0^2" "c2 = a1^2*b0^2"
                    "c1 = a1^2*b1^2" "c2 = a0^2*b1^2"
          using c1_def c2_def eq1 eq2 by algebra+

        have "c1 * (a0^2 + b0^2 - 1)  = c1 * (a1^2 + b1^2 - 1)"
          using in_aff c_eqs 
          unfolding e'_aff_def e'_def
          by(simp add: a1_nz a0_nz)
        then have eq3: "(c1-c2) * (a0^2-b1^2) = 0"
                       "(c1-c2) * (a1^2-b0^2) = 0"
          apply(simp_all add: algebra_simps)
          unfolding c1_def c2_def
          using c_eqs by algebra+
        then consider
          (1) "c1 = c2" |
          (2) "a0^2 - b1^2 = 0" "a1^2-b0^2 = 0" by force
        then have "(a0,b0) \<in> {(b1,a1),(-b1,-a1)}"
        proof(cases)
          case 1
          then have "b0^2 = b1^2" "a0^2 = a1^2"
            using c_eqs a0_nz a1_nz by auto      
          then have "b0 = b1 \<or> b0 = -b1" "a0 = a1 \<or> a0 = -a1"
            by algebra+
          then show ?thesis
            using eq2 eq1 a0_nz(1) a1_nz(2) nonzero_mult_div_cancel_left 
                  two_not_zero by force
        next
          case 2
          then show ?thesis 
            using eq2 by algebra
        qed
        then  have "(a0,b0) \<in> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
          using p_expr by auto
        then have "(\<exists> g \<in> rotations. \<tau> q = (g \<circ> i) p)"
          unfolding rotations_def by (simp add: \<open>\<tau> q = (a0, b0)\<close>)
        then obtain g where "g \<in> rotations \<and> \<tau> q = (g \<circ> i) p"
          by blast
        then have "q = (\<tau> \<circ> g \<circ> i) p"
          using tau_sq \<open>\<tau> q = (a0, b0)\<close> q_def by auto
        then show ?thesis
          unfolding symmetries_def rotations_def 
          using tau_rot_sym \<open>g \<in> rotations \<and> \<tau> q = (g \<circ> i) p\<close> symmetries_def by blast  
    qed
    next
      case False  
      then have t1: "delta_plus a1 b1 (fst q) (snd q) = 0" 
        using \<open>delta x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> delta_def p_def q_def by auto
      then show ?thesis 
      proof(cases "\<delta>_minus a0 b0 = 0")
        case True
        then have cas1: "delta_plus a1 b1 (fst q) (snd q) = 0"
                        "\<delta>_minus a0 b0 = 0" using t1 by auto
        have \<delta>'_expr: "p\<delta>' a0 b0 = a0 * b0 + a1 * b1"
          unfolding p\<delta>'_def delta_plus_def 
          by(simp add: algebra_simps a0_nz a1_nz power2_eq_square[symmetric] t_expr d_nz)
        
        have eq1': "a0 * b0 + a1 * b1 = 0"
          using \<delta>'_expr cas1(1) p\<delta>'_def q_def tau_sq tq_expr by auto 
        then have eq1: "a0 = - (a1 * b1) / b0"  
          using a0_nz(2) 
          by(simp add: divide_simps,algebra) 
        have eq2: "b0^2 - b1^2 = 0"
          using cas1(2) unfolding \<delta>_minus_def delta_y_def  
          by(simp add: divide_simps t_nz a0_nz a1_nz eq1 power2_eq_square[symmetric])
        have eq3: "a0^2 - a1^2 = 0" 
          using eq2 eq1'
          by(simp add: algebra_simps divide_simps a0_nz a1_nz eq1 power2_eq_square)
        
        from eq2 have pos1: "b0 = b1 \<or> b0 = -b1" by algebra
        from eq3 have pos2: "a0 = a1 \<or> a0 = -a1" by algebra
        have "(a0 = a1 \<and> b0 = -b1) \<or> (a0 = -a1 \<and> b0 = b1)"
          using pos1 pos2 eq2 eq3 eq1' by fastforce 
        then have "(a0,b0) = (a1,-b1) \<or> (a0,b0) = (-a1,b1)" by auto        
        then have "(a0,b0) \<in> {(a1,-b1),(-a1,b1)}" by simp
        moreover have "{(a1,-b1),(-a1,b1)} \<subseteq> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
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
        then have cas2: "delta_plus a1 b1 (fst q) (snd q) = 0"
                         "\<delta>_plus a0 b0 = 0"               
          using t1 False \<delta>_minus_def \<delta>_plus_def \<open>delta' x1 y1 x2 y2 = 0\<close> \<open>p = (a1, b1)\<close> 
                delta'_def p_def q_def tq_expr by auto
        have \<delta>'_expr: "p\<delta>' a0 b0 = a0*b0 + a1*b1"
          unfolding p\<delta>'_def delta_plus_def 
          by(simp add: algebra_simps a0_nz a1_nz power2_eq_square[symmetric] t_expr d_nz)
        then have eq1: "a0*b0 + a1*b1 = 0" 
          using p\<delta>'_def \<delta>'_expr tq_expr q_def tau_sq cas2(1) by force

        have eq2: "b0 * b1 - a0 * a1 = 0" 
          using cas2 unfolding \<delta>_plus_def delta_x_def 
          by(simp add: algebra_simps t_nz a0_nz)  

        define c1 where "c1 = a0^2*b0^2" 
        define c2 where "c2 = a0^2*a1^2"
        have c_eqs: "c1 = a0^2*b0^2" "c2 = a0^2*a1^2"
                    "c1 = a1^2*b1^2" "c2 = b0^2*b1^2"
          using c1_def c2_def eq1 eq2 by algebra+

        have "c1 * (a0^2 + b0^2 - 1)  = c1 * (a1^2 + b1^2 - 1)"
          using in_aff c_eqs 
          unfolding e'_aff_def e'_def
          by(simp add: a1_nz a0_nz)
        then have eq3: "(c1-c2) * (a0^2-a1^2) = 0"
                       "(c1-c2) * (b0^2-b1^2) = 0"
          apply(simp_all add: algebra_simps)
          unfolding c1_def c2_def
          using c_eqs by algebra+

        then consider
          (1) "c1 = c2" |
          (2) "a0^2-a1^2 = 0" "b0^2-b1^2 = 0" by force
        then have "(a0,b0) \<in> {(b1,a1),(-b1,-a1)}"
        proof(cases)
          case 1
          then have "b0^2 = a1^2" "a0^2 = b1^2"
            using c_eqs a0_nz a1_nz by auto 
          then show ?thesis
            using eq2 by algebra          
        next
          case 2
          then have "b0 = b1 \<or> b0 = -b1" "a0 = a1 \<or> a0 = -a1"
            by algebra+
          then show ?thesis
            using eq1 eq2 False \<delta>_minus_def a1_nz(1) a1_nz(2) delta_y_def by auto
        qed
        then have "(a0,b0) \<in> {i p, (\<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> i) p, (\<rho> \<circ> \<rho> \<circ> \<rho> \<circ> i) p}"
          unfolding p_expr by auto

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
    qed
    then show ?thesis 
      using \<open>p \<in> e_circ\<close> by blast
  qed
qed

lemma dichotomy_2:
  assumes "add (x1,y1) (x2,y2) = (1,0)" 
          "((x1,y1),(x2,y2)) \<in> e'_aff_0"
  shows "(x2,y2) = i (x1,y1)"
proof -
  have 1: "x1 = x2"
    using assms(1,2) unfolding e'_aff_0_def e'_aff_def delta_def delta_plus_def 
                               delta_minus_def e'_def
    apply(simp) 
    apply(simp add: c_eq_1 t_expr) 
    by algebra

  have 2: "y1 = - y2"
    using assms(1,2) unfolding e'_aff_0_def e'_aff_def delta_def delta_plus_def 
                               delta_minus_def e'_def
    apply(simp) 
    apply(simp add: c_eq_1 t_expr)
    by algebra

  from 1 2 show ?thesis by simp
qed
  
(*TODO: once the field is generalized, algebra stops automatically solving this goal*)       
lemma dichotomy_3:
  assumes "ext_add (x1,y1) (x2,y2) = (1,0)" 
          "((x1,y1),(x2,y2)) \<in> e'_aff_1"
  shows "(x2,y2) = i (x1,y1)"
proof -
  have nz: "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" 
    using assms by(simp,force)+
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff"
    using assms unfolding e'_aff_1_def by auto
  have ds: "delta' x1 y1 x2 y2 \<noteq> 0"
    using assms unfolding e'_aff_1_def by auto

  have eqs: "x1*(y1+y2) = x2*(y1+y2)" "x1 * y1 + x2 * y2 = 0" 
    using assms in_aff ds
    unfolding e'_aff_def e'_def delta'_def delta_x_def delta_y_def
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
  apply(simp add: c_eq_1)
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
               ((x0,y0) \<in> e'_aff \<and> (x1,y1) \<in> e'_aff) \<and>
               ((x0 \<noteq> 0 \<and> y0 \<noteq> 0 \<and> (x1,y1) = \<tau> (x0,y0) \<and> j = l+1) \<or>
                (x0 = x1 \<and> y0 = y1 \<and> l = j))}"

lemma gluing_char:
  assumes "(((x0,y0),l),((x1,y1),j)) \<in> gluing"
  shows "((x0,y0) = (x1,y1) \<and> l = j) \<or> ((x1,y1) = \<tau> (x0,y0) \<and> l = j+1 \<and> x0 \<noteq> 0 \<and> y0 \<noteq> 0)"
  using assms gluing_def by force+

lemma gluing_char_zero:
  assumes "(((x0,y0),l),((x1,y1),j)) \<in> gluing" "x0 = 0 \<or> y0 = 0"
  shows "(x0,y0) = (x1,y1) \<and> l = j"
  using assms unfolding gluing_def e_circ_def by force

lemma gluing_aff:
  assumes "(((x0,y0),l),((x1,y1),j)) \<in> gluing"
  shows "(x0,y0) \<in> e'_aff" "(x1,y1) \<in> e'_aff"
  using assms unfolding gluing_def by force+

definition e'_aff_bit :: "(('a \<times> 'a) \<times> bit) set" where
 "e'_aff_bit = e'_aff \<times> UNIV"

lemma eq_rel: "equiv e'_aff_bit gluing"
  unfolding equiv_def
proof(safe)
  show "refl_on e'_aff_bit gluing"
    unfolding refl_on_def e'_aff_bit_def gluing_def by auto
  show "sym gluing" 
    unfolding sym_def gluing_def by(auto simp add: e_circ_def t_nz)
  show "trans gluing"
    unfolding trans_def gluing_def by(auto simp add: e_circ_def t_nz)
qed

definition e_proj where "e_proj = e'_aff_bit // gluing"

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
  assumes "x = 0 \<or> y = 0" "(x,y) \<in> e'_aff"
  shows "gluing `` {((x,y), l)} = {((x,y), l)}"
proof - 
  have "(x,y) \<notin> e_circ" using assms unfolding e_circ_def by blast 
  then show ?thesis
    using assms unfolding gluing_def Image_def
    by(simp split: prod.splits del: \<tau>.simps add: assms,safe)
qed

lemma gluing_class_2:
  assumes "x \<noteq> 0" "y \<noteq> 0" "(x,y) \<in> e'_aff"
  shows "gluing `` {((x,y), l)} = {((x,y), l), (\<tau> (x,y), l + 1)}"
proof - 
  have "(x,y) \<in> e_circ" using assms unfolding e_circ_def by blast
  then have "\<tau> (x,y) \<in> e'_aff"
    using \<tau>_circ using e_circ_def by force
   show ?thesis
    using assms unfolding gluing_def Image_def
    apply(simp add: e_circ_def assms del: \<tau>.simps,safe) 
    using \<open>\<tau> (x,y) \<in> e'_aff\<close> by argo 
qed

lemma e_proj_elim_1:
  assumes "(x,y) \<in> e'_aff"
  shows "{((x,y),l)} \<in> e_proj \<longleftrightarrow> x = 0 \<or> y = 0"
proof
  assume as: "{((x, y), l)} \<in> e_proj" 
  have eq: "gluing `` {((x, y), l)} = {((x,y),l)}"
    (is "_ = ?B")
   using quotientI[of _ ?B gluing] eq_class_simp as by auto
  then show "x = 0 \<or> y = 0" 
    using assms gluing_class_2 by force
next
  assume "x = 0 \<or> y = 0"
  then have eq: "gluing `` {((x, y), l)} = {((x,y),l)}"
    using assms gluing_class_1 by presburger
  show "{((x,y),l)} \<in> e_proj"
    apply(subst eq[symmetric])  
    unfolding e_proj_def apply(rule quotientI)
    unfolding e'_aff_bit_def using assms by simp  
qed

lemma e_proj_elim_2:
  assumes "(x,y) \<in> e'_aff"
  shows "{((x,y),l),(\<tau> (x,y),l+1)} \<in> e_proj \<longleftrightarrow> x \<noteq> 0 \<and> y \<noteq> 0"
proof 
  assume "x \<noteq> 0 \<and> y \<noteq> 0"
  then have eq: "gluing `` {((x, y), l)} = {((x,y),l),(\<tau> (x,y),l+1)}"
    using assms gluing_class_2 by presburger
  show "{((x,y),l),(\<tau> (x,y),l+1)} \<in> e_proj"
    apply(subst eq[symmetric])  
    unfolding e_proj_def apply(rule quotientI)
    unfolding e'_aff_bit_def using assms by simp  
next
  assume as: "{((x, y), l), (\<tau> (x, y), l + 1)} \<in> e_proj" 
  have eq: "gluing `` {((x, y), l)} = {((x,y),l),(\<tau> (x,y),l+1)}"
    (is "_ = ?B")
   using quotientI[of _ ?B gluing] eq_class_simp as by auto
  then show "x \<noteq> 0 \<and> y \<noteq> 0" 
    using assms gluing_class_1 by auto
qed

lemma e_proj_eq:
  assumes "p \<in> e_proj"
  shows "\<exists> x y l. (p = {((x,y),l)} \<or> p = {((x,y),l),(\<tau> (x,y),l+1)}) \<and> (x,y) \<in> e'_aff"      
proof -
  obtain g where p_expr: "p = gluing `` {g}" "g \<in> e'_aff_bit"
    using assms unfolding e_proj_def quotient_def by blast+
  then obtain x y l where g_expr: "g = ((x,y),l)" "(x,y) \<in> e'_aff" 
    using e'_aff_bit_def by auto
  show ?thesis
    using e_proj_elim_1 e_proj_elim_2 gluing_class_1 gluing_class_2 g_expr p_expr by meson
qed

lemma e_proj_aff:
  "gluing `` {((x,y),l)} \<in> e_proj \<longleftrightarrow> (x,y) \<in> e'_aff"
proof 
  assume "gluing `` {((x, y), l)} \<in> e_proj"
  then show "(x,y) \<in> e'_aff"
    unfolding e_proj_def e'_aff_bit_def 
    apply(rule quotientE)
    using eq_equiv_class gluing_aff 
          e'_aff_bit_def eq_rel by fastforce
next
  assume as: "(x, y) \<in> e'_aff"
  show "gluing `` {((x, y), l)} \<in> e_proj"
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
  have "(x0,y0) \<in> e'_aff"
    using assms e_proj_aff by simp
  have "gluing `` {((x0,y0),l)} = {((x0,y0),l)} \<or> 
        gluing `` {((x0,y0),l)} = {((x0,y0),l),(\<tau> (x0,y0),l+1)}"
    using assms gluing_class_1 gluing_class_2 \<open>(x0, y0) \<in> e'_aff\<close> by meson   
  then show ?thesis using assms by fast
qed

lemma gluing_cases_points:
  assumes "x \<in> e_proj" "x = gluing `` {(p,l)}"
  shows "x = {(p,l)} \<or> x = {(p,l),(\<tau> p,l+1)}"  
  using gluing_cases_explicit[OF assms(1), of "fst p" "snd p" l] assms by auto



lemma identity_equiv: 
  "gluing `` {((1, 0), l)} = {((1,0),l)}"
  unfolding Image_def
proof(simp,standard)
  show "{y. (((1, 0), l), y) \<in> gluing} \<subseteq> {((1, 0), l)}"    
    using gluing_char_zero by(intro subrelI,fast) 
  have "(1,0) \<in> e'_aff" 
    unfolding e'_aff_def e'_def by simp
  then have "((1, 0), l) \<in> e'_aff_bit"
    using zero_bit_def unfolding e'_aff_bit_def  by blast
  show "{((1, 0), l)} \<subseteq> {y. (((1, 0), l), y) \<in> gluing}"
    using eq_rel \<open>((1, 0), l) \<in> e'_aff_bit\<close> 
    unfolding equiv_def refl_on_def by blast
qed

lemma identity_proj:
  "{((1,0),l)} \<in> e_proj"
proof -
  have "(1,0) \<in> e'_aff"
    unfolding e'_aff_def e'_def by auto
  then show ?thesis
    using e_proj_aff[of 1 0 l] identity_equiv by auto
qed
  
lemma gluing_inv:
  assumes "x \<noteq> 0" "y \<noteq> 0" "(x,y) \<in> e'_aff"
  shows "gluing `` {((x,y),j)} = gluing `` {(\<tau> (x,y),j+1)}"
proof -
  have taus: "\<tau> (x,y) \<in> e'_aff" 
    using e_circ_def assms \<tau>_circ by fastforce+ 

  have "gluing `` {((x,y), j)} =  {((x, y), j), (\<tau> (x, y), j + 1)}"
    using gluing_class_2 assms by meson
  also have "... = {(\<tau> (x, y), j+1), (\<tau> (\<tau> (x, y)), j)}"
    using tau_idemp_explicit by force
  also have "{(\<tau> (x, y), j+1), (\<tau> (\<tau> (x, y)), j)} = gluing `` {(\<tau> (x,y), j + 1)}"
    apply(subst gluing_class_2[of "fst (\<tau> (x,y))" "snd (\<tau> (x,y))",
          simplified prod.collapse])
    using assms taus t_nz by auto
  finally show ?thesis by blast
qed 


subsection \<open>Projective addition on points\<close>


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

lemma proj_add_inv:
  assumes "(x0,y0) \<in> e'_aff"
  shows "proj_add ((x0,y0),l) (i (x0,y0),l') = ((1,0),l+l')"
proof -
  have i_in: "i (x0,y0) \<in> e'_aff"
    using i_aff assms by blast

  consider (1) "x0 = 0" | (2) "y0 = 0" | (3) "x0 \<noteq> 0" "y0 \<noteq> 0" by fast
  then show ?thesis
  proof(cases)
    case 1
    from assms 1 have y_expr: "y0 = 1 \<or> y0 = -1" 
      unfolding e'_aff_def e'_def by(simp,algebra) 
    then have "delta x0 y0 x0 (-y0) \<noteq> 0"
      using 1 unfolding delta_def delta_minus_def delta_plus_def by simp
    then show "proj_add ((x0,y0),l) (i (x0,y0),l') = ((1,0),l+l')"  
      using 1  assms delta_plus_def i_in inverse_generalized by fastforce     
  next
    case 2
    from assms 2 have "x0 = 1 \<or> x0 = -1" 
      unfolding e'_aff_def e'_def by(simp,algebra) 
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
        using assms t_expr unfolding e'_aff_def e'_def power2_eq_square by force
      then have "2*x0^2 = 2 \<or> 2*x0^2 = 0"
        by algebra
      then have "x0 = 1 \<or> x0 = -1"
        using 3 
        apply(simp add: two_not_zero) 
        by algebra
      then have "y0 = 0"
        using assms t_n1 t_nm1
        unfolding e'_aff_def e'_def 
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
  "proj_add ((x0,y0),l) ((x1,y1),j) = proj_add ((x1,y1),j) ((x0,y0),l)"
proof -
  consider 
   (1) "delta x0 y0 x1 y1 \<noteq> 0 \<and> (x0,y0)  \<in> e'_aff \<and> (x1,y1) \<in> e'_aff" |
   (2) "delta' x0 y0 x1 y1 \<noteq> 0 \<and> (x0,y0)  \<in> e'_aff \<and> (x1,y1) \<in> e'_aff" |
   (3) "(delta x0 y0 x1 y1 = 0 \<and> delta' x0 y0 x1 y1 = 0) \<or> 
         (x0,y0) \<notin> e'_aff \<or> (x1,y1) \<notin> e'_aff" by blast
  then show ?thesis
  proof(cases)
    case 1 then show ?thesis by(simp add: commutativity delta_com)  
  next
    case 2 then show ?thesis by(simp add: ext_add_comm delta'_com del: ext_add.simps)  
  next
    case 3 then show ?thesis by(auto simp add: delta_com delta'_com)
  qed    
qed

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
              "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    by blast
  then have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff"  by auto
  from p_q_expr have gluings: "p = (gluing `` {((x,y),l)})" 
                              "q = (gluing `` {((x',y'),l')})"    
    using assms e_proj_elim_1 e_proj_elim_2 gluing_class_1 gluing_class_2
    by metis+
  then have gluing_proj: "(gluing `` {((x,y),l)}) \<in> e_proj"
                         "(gluing `` {((x',y'),l')}) \<in> e_proj" 
    using assms by blast+

  consider 
     "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | "((x, y), x', y') \<in> e'_aff_0" 
   | "((x, y), x', y') \<in> e'_aff_1"
    using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by blast
  then show ?thesis 
  proof(cases)
    case 1
    then obtain r where r_expr: "(x',y') = (\<tau> \<circ> r) (i (x,y))" "r \<in> rotations"
      using sym_decomp by force

    then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
      using 1 t_nz unfolding e_circ_def rotations_def by force+

    have taus: "\<tau> (x',y') \<in> e'_aff" 
      using nz i_aff p_q_expr(3) r_expr rot_aff tau_idemp_point by auto

    have circ: "(x,y) \<in> e_circ" 
      using nz in_aff e_circ_def by blast

    have p_q_expr': "p = {((x,y),l),(\<tau> (x,y),l+1)}"
                    "q = {(\<tau> (x',y'),l'+1),((x',y'),l')}"
      using gluings nz gluing_class_2 taus in_aff tau_idemp_point t_nz assms by auto

    have p_q_proj: "{((x,y),l),(\<tau> (x,y),l+1)} \<in> e_proj" 
                   "{(\<tau> (x',y'),l'+1),((x',y'),l')} \<in> e_proj" 
      using p_q_expr' assms by auto

    consider
     (a)  "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (x', y') = (g \<circ> i) (x, y))" 
    |(b)  "((x, y), \<tau> (x', y')) \<in> e'_aff_0" 
    |(c)  "((x, y), \<tau> (x', y')) \<in> e'_aff_1"
      using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>\<tau> (x', y') \<in> e'_aff\<close>] by blast  
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
        unfolding e'_aff_0_def by simp 
      then have 
        add_some: "proj_add ((x,y),l) (\<tau> (x',y'),l'+1) = (add (x, y) (\<tau> (x',y')), l+l'+1)"
        using proj_add.simps[of x y _ _ l "l'+1", OF _ ] 
              \<open>(x,y) \<in> e'_aff\<close> \<open>\<tau> (x', y') \<in> e'_aff\<close> by force 
      then show ?thesis
        unfolding p_q_expr' proj_add_class.simps(1)[OF p_q_proj] 
        unfolding e'_aff_0_def using ds in_aff taus by force
    next
      case c
      then have ds: "delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
        unfolding e'_aff_1_def by simp 
      then have 
        add_some: "proj_add ((x,y),l) (\<tau> (x',y'),l'+1) = (ext_add (x, y) (\<tau> (x',y')), l+l'+1)"
        using proj_add.simps[of x y _ _ l "l'+1", OF _ ] 
              \<open>(x,y) \<in> e'_aff\<close> \<open>\<tau> (x', y') \<in> e'_aff\<close> by force 
      then show ?thesis
        unfolding p_q_expr' proj_add_class.simps(1)[OF p_q_proj] 
        unfolding e'_aff_1_def using ds in_aff taus by force
  qed
  next
    case 2
    then have ds: "delta x y x' y' \<noteq> 0" 
      unfolding e'_aff_0_def by simp
    then have
      add_some: "proj_add ((x,y),l) ((x',y'),l') = (add (x, y) (x',y'), l+l')"
      using proj_add.simps(1)[of x y x' y' l "l'", OF _ ] in_aff by blast
    then show ?thesis 
      using p_q_expr 
      unfolding  proj_add_class.simps(1)[OF assms] 
      unfolding e'_aff_0_def using ds in_aff by fast
  next
    case 3
    then have ds: "delta' x y x' y' \<noteq> 0" 
      unfolding e'_aff_1_def by simp
    then have
      add_some: "proj_add ((x,y),l) ((x',y'),l') = (ext_add (x, y) (x',y'), l+l')"
      using proj_add.simps(2)[of x y x' y' l "l'", OF _ ] in_aff by blast
    then show ?thesis 
      using p_q_expr 
      unfolding  proj_add_class.simps(1)[OF assms] 
      unfolding e'_aff_1_def using ds in_aff by fast
  qed
qed

lemma covering_with_deltas:
  assumes "(gluing `` {((x,y),l)}) \<in> e_proj" "(gluing `` {((x',y'),l')}) \<in> e_proj"
  shows "delta x y x' y' \<noteq> 0 \<or> delta' x y x' y' \<noteq> 0 \<or>
         delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0 \<or>
         delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
proof -
  define p where "p = (gluing `` {((x,y),l)})"
  define q where "q = (gluing `` {((x',y'),l')})"
  have "p \<in> e'_aff_bit // gluing"
    using assms(1) p_def unfolding e_proj_def by blast
  from e_proj_eq[OF assms(1)] e_proj_eq[OF assms(2)]
  have
    p_q_expr: "p = {((x, y), l)} \<or> p = {((x, y), l), (\<tau> (x, y), l + 1)} " 
    "q = {((x', y'), l')} \<or> q = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
    "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using p_def q_def 
    using assms(1) gluing_cases_explicit apply auto[1]
    using assms(2) gluing_cases_explicit q_def apply auto[1] 
    using assms(1) e'_aff_bit_def e_proj_def eq_rel gluing_cases_explicit in_quotient_imp_subset apply fastforce
    using assms(2) e'_aff_bit_def e_proj_def eq_rel gluing_cases_explicit in_quotient_imp_subset by fastforce
  then have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff"  by auto

  then have gluings: "p = (gluing `` {((x,y),l)})" 
                     "q = (gluing `` {((x',y'),l')})"
    using p_def q_def by simp+

  then have gluing_proj: "(gluing `` {((x,y),l)}) \<in> e_proj"
                         "(gluing `` {((x',y'),l')}) \<in> e_proj" 
    using assms by blast+

  consider 
     "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | "((x, y), x', y') \<in> e'_aff_0" 
   | "((x, y), x', y') \<in> e'_aff_1"
    using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by blast
  then show ?thesis 
  proof(cases)
    case 1
    then obtain r where r_expr: "(x',y') = (\<tau> \<circ> r) (i (x,y))" "r \<in> rotations"
      using sym_decomp by force

    then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
      using 1 t_nz unfolding e_circ_def rotations_def by force+

    have taus: "\<tau> (x',y') \<in> e'_aff" 
      using nz i_aff p_q_expr(3) r_expr rot_aff tau_idemp_point by auto

    have circ: "(x,y) \<in> e_circ" 
      using nz in_aff e_circ_def by blast

    have p_q_expr': "p = {((x,y),l),(\<tau> (x,y),l+1)}"
                    "q = {(\<tau> (x',y'),l'+1),((x',y'),l')}"
      using gluings nz gluing_class_2 taus in_aff tau_idemp_point t_nz assms by auto

    have p_q_proj: "{((x,y),l),(\<tau> (x,y),l+1)} \<in> e_proj" 
                   "{(\<tau> (x',y'),l'+1),((x',y'),l')} \<in> e_proj" 
      using p_q_expr p_q_expr' assms gluing_proj gluings by auto

    consider
      (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (x', y') = (g \<circ> i) (x, y))" 
    | (b) "((x, y), \<tau> (x', y')) \<in> e'_aff_0" 
    | (c) "((x, y), \<tau> (x', y')) \<in> e'_aff_1"
      using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>\<tau> (x', y') \<in> e'_aff\<close>] by blast  
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
        unfolding e'_aff_0_def using x''_def y''_def by simp 
      then show ?thesis
        unfolding x''_def y''_def by blast
    next
      case c
      define x'' where "x'' = fst (\<tau> (x',y'))"
      define y'' where "y'' = snd (\<tau> (x',y'))"
      from c have "delta' x y x'' y'' \<noteq> 0"
        unfolding e'_aff_1_def using x''_def y''_def by simp 
      then show ?thesis
        unfolding x''_def y''_def by blast
  qed
  next
    case 2
    then have "delta x y x' y' \<noteq> 0" 
      unfolding e'_aff_0_def by simp
    then show ?thesis by simp
  next
    case 3
    then have "delta' x y x' y' \<noteq> 0" 
      unfolding e'_aff_1_def by simp
    then show ?thesis by simp
  qed
qed

subsubsection \<open>Independence of the representant\<close>


(* TODO: this does not use independence of the representant *)
lemma proj_add_class_comm:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj" 
  shows "proj_add_class c1 c2 = proj_add_class c2 c1"
proof - 
  have "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1 \<Longrightarrow> 
        ((x2, y2), x1, y1) \<in> e'_aff_0 \<union> e'_aff_1" for x1 y1 x2 y2
    unfolding e'_aff_0_def e'_aff_1_def
              e'_aff_def e'_def 
              delta_def delta_plus_def delta_minus_def
              delta'_def delta_x_def delta_y_def 
    by(simp,algebra) 
  then have "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
     ((x1, y1), i) \<in> c1 \<and> ((x2, y2), j) \<in> c2 \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
        {proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
     ((x1, y1), i) \<in> c2 \<and> ((x2, y2), j) \<in> c1 \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1}"
    using proj_add_comm by blast
  then show ?thesis   
    unfolding proj_add_class.simps(1)[OF assms]
                proj_add_class.simps(1)[OF assms(2) assms(1)] by argo
qed



lemma gluing_add_1: 
  assumes "gluing `` {((x,y),l)} = {((x, y), l)}" "gluing `` {((x',y'),l')} = {((x', y'), l')}" 
          "gluing `` {((x,y),l)} \<in> e_proj" "gluing `` {((x',y'),l')} \<in> e_proj" "delta x y x' y' \<noteq> 0"
  shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')}) = (gluing `` {(add (x,y) (x',y'),l+l')})"
proof -
  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have add_in: "add (x, y) (x', y') \<in> e'_aff"
    using add_closure \<open>delta x y x' y' \<noteq> 0\<close> delta_def e_e'_iff e'_aff_def by auto
  from in_aff have zeros: "x = 0 \<or> y = 0" "x' = 0 \<or> y' = 0"
    using e_proj_elim_1 assms by presburger+
  then have add_zeros: "fst (add (x,y) (x',y')) = 0 \<or> snd (add (x,y) (x',y')) = 0"
    by auto
  then have add_proj: "gluing `` {(add (x, y) (x', y'), l + l')} = {(add (x, y) (x', y'), l + l')}" 
    using add_in gluing_class_1 by auto
  have e_proj: "gluing `` {((x,y),l)} \<in> e_proj"
               "gluing `` {((x',y'),l')} \<in> e_proj"
               "gluing `` {(add (x, y) (x', y'), l + l')} \<in> e_proj"
    using e_proj_aff in_aff add_in by auto
    
  consider
    (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
    (b) "((x, y), x', y') \<in> e'_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
    (c) "((x, y), x', y') \<in> e'_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e'_aff_0"
    using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by argo
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
      unfolding assms(1,2) e'_aff_0_def
      using \<open>delta x y x' y' \<noteq> 0\<close> in_aff
      apply(simp add: add_eq del: add.simps)
      apply(subst eq_class_simp)
      using add_proj e_proj by auto
  next
    case c
    then have eqs: "delta x y x' y' = 0" "delta' x y x' y' \<noteq> 0" "e x y = 0" "e x' y' = 0"
      unfolding e'_aff_0_def e'_aff_1_def apply fast+
      using e_e'_iff in_aff unfolding e'_aff_def by fast+
    then show ?thesis using assms  by simp
  qed
qed

lemma gluing_add_2:
  assumes "gluing `` {((x,y),l)} = {((x, y), l)}" "gluing `` {((x',y'),l')} = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" 
          "gluing `` {((x,y),l)} \<in> e_proj" "gluing `` {((x',y'),l')} \<in> e_proj" "delta x y x' y' \<noteq> 0"
  shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')}) = (gluing `` {(add (x,y) (x',y'),l+l')})"
proof -
  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have add_in: "add (x, y) (x', y') \<in> e'_aff"
    using add_closure \<open>delta x y x' y' \<noteq> 0\<close> delta_def e_e'_iff e'_aff_def by auto
  from in_aff have zeros: "x = 0 \<or> y = 0" "x' \<noteq> 0"  "y' \<noteq> 0"
    using e_proj_elim_1 e_proj_elim_2 assms by presburger+
  have e_proj: "gluing `` {((x,y),l)} \<in> e_proj"
               "gluing `` {((x',y'),l')} \<in> e_proj"
               "gluing `` {(add (x, y) (x', y'), l + l')} \<in> e_proj"
    using e_proj_aff in_aff add_in by auto

  consider
      (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
      (b) "((x, y), x', y') \<in> e'_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
      (c) "((x, y), x', y') \<in> e'_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e'_aff_0"
      using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by fast
  then show ?thesis
  proof(cases)
    case a
    then have "False"
      using in_aff zeros unfolding e_circ_def by force
    then show ?thesis by simp
  next
    case b
    then have ld_nz: "delta x y x' y' \<noteq> 0" unfolding e'_aff_0_def by auto    

    have v1: "proj_add ((x, y), l) ((x', y'), l') = (add (x, y) (x', y'), l + l')"
      by(simp add: \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>  ld_nz del: add.simps)

    have ecirc: "(x',y') \<in> e_circ" "x' \<noteq> 0" "y' \<noteq> 0"
      unfolding e_circ_def using zeros \<open>(x',y') \<in> e'_aff\<close> by blast+
    then have "\<tau> (x', y') \<in> e_circ" 
      using zeros \<tau>_circ by blast
    then have in_aff': "\<tau> (x', y') \<in> e'_aff"
      unfolding e_circ_def by force

    have add_nz: "fst (add (x, y) (x', y')) \<noteq> 0" 
                 "snd (add (x, y) (x', y')) \<noteq> 0" 
      using zeros ld_nz in_aff
      unfolding delta_def delta_plus_def delta_minus_def e'_aff_def e'_def
      apply(simp_all)
      apply(simp_all add: c_eq_1)
      by auto

    have add_in: "add (x, y) (x', y') \<in> e'_aff"
      using add_closure in_aff e_e'_iff ld_nz unfolding e'_aff_def delta_def by simp

    have ld_nz': "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
      unfolding delta_def delta_plus_def delta_minus_def
      using zeros by fastforce
    
    have tau_conv: "\<tau> (add (x, y) (x', y')) = add (x, y) (\<tau> (x', y'))"
      using zeros e'_aff_x0[OF _ in_aff(1)] e'_aff_y0[OF _ in_aff(1)] 
      apply(simp_all)
      apply(simp_all add: c_eq_1 divide_simps d_nz t_nz)
      apply(elim disjE) 
      apply(simp_all add: t_nz zeros) 
      by auto

    have v2: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (add (x, y) (x', y')), l+l'+1)"
      using proj_add.simps \<open>\<tau> (x', y') \<in> e'_aff\<close> in_aff tau_conv 
            \<open>delta x y (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0\<close> by auto    
     
    have gl_class: "gluing `` {(add (x, y) (x', y'), l + l')} =
                {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}"
           "gluing `` {(add (x, y) (x', y'), l + l')} \<in> e_proj" 
      using gluing_class_2 add_nz add_in apply simp
      using e_proj_aff add_in by auto
   
    show ?thesis          
    proof -
      have "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and>
       ((x1, y1), x2, y2)
       \<in> {((x1, y1), x2, y2). (x1, y1) \<in> e'_aff \<and> (x2, y2) \<in> e'_aff \<and> delta x1 y1 x2 y2 \<noteq> 0} \<union> e'_aff_1} =
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
       unfolding assms(1,2) gl_class e'_aff_0_def
       apply(subst eq)
       apply(subst eq_class_simp)
       using gl_class by auto
   qed
  next
   case c
    have ld_nz: "delta x y x' y' = 0" 
     using \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close> c
     unfolding e'_aff_0_def by force
    then have "False"
      using assms e_proj_elim_1 in_aff
      unfolding delta_def delta_minus_def delta_plus_def by blast
    then show ?thesis by blast
  qed    
qed   

lemma gluing_add_4: 
  assumes "gluing `` {((x, y), l)} = {((x, y), l), (\<tau> (x, y), l + 1)}" 
          "gluing `` {((x', y'), l')} = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}"
          "gluing `` {((x, y), l)} \<in> e_proj" "gluing `` {((x', y'), l')} \<in> e_proj" "delta x y x' y' \<noteq> 0"
  shows "proj_addition (gluing `` {((x, y), l)}) (gluing `` {((x', y'), l')}) = 
         gluing `` {(add (x, y) (x',y'), l+l')}"
 (is "proj_addition ?p ?q = _")
proof -
  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff"
    using e_proj_aff assms by meson+
  then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
    using assms e_proj_elim_2 by auto
  then have circ: "(x,y) \<in> e_circ" "(x',y') \<in> e_circ"
    using in_aff e_circ_def nz by auto
  then have taus: "(\<tau> (x', y')) \<in> e'_aff" "(\<tau> (x, y)) \<in> e'_aff" "\<tau> (x', y') \<in> e_circ"
    using \<tau>_circ circ_to_aff by auto

  consider 
   (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (b) "((x, y), x', y') \<in> e'_aff_0" 
   | (c) "((x, y), x', y') \<in> e'_aff_1" "((x, y), x', y') \<notin> e'_aff_0" 
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
      unfolding e'_aff_0_def by auto    
    then have ds: "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" 
      unfolding delta_def delta_plus_def delta_minus_def 
      apply(simp add: algebra_simps power2_eq_square[symmetric])
      unfolding t_expr[symmetric]
      by(simp add: field_simps)
    have v1: "proj_add ((x, y), l) ((x', y'), l') = (add (x, y) (x', y'), l + l')"
      using ld_nz proj_add.simps \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close> by simp
    have v2: "proj_add (\<tau> (x, y), l+1) (\<tau> (x', y'), l'+1) = (add (x, y) (x', y'), l + l')"
      using ds proj_add.simps taus
            inversion_invariance_1 nz tau_idemp proj_add.simps
      by (simp add: c_eq_1 t_nz)

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
        apply(simp add: c_eq_1)
        using aaa in_aff ld_nz 
        unfolding e'_aff_def e'_def delta_def delta_minus_def delta_plus_def 
        apply(safe)
        apply(simp_all add: divide_simps t_nz nz)
         apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr d_nz)
        unfolding t_expr[symmetric]
        by algebra+
      
      have v3: 
        "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (add (x, y) (x', y')), l+l'+1)" 
        using proj_add.simps \<open>(\<tau> (x', y')) \<in> e'_aff\<close> 
        apply(simp del: add.simps \<tau>.simps)
        using tau_conv tau_idemp_explicit 
              proj_add.simps(1)[OF aaa \<open>(x,y) \<in> e'_aff\<close>,simplified prod.collapse,OF \<open>(\<tau> (x', y')) \<in> e'_aff\<close>] 
        by (metis (no_types, lifting) add.assoc prod.collapse)

      have ds': "delta (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' \<noteq> 0"
        using aaa unfolding delta_def delta_plus_def delta_minus_def
        apply(simp add: t_nz nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)
        by(simp add: divide_simps nz t_nz)

      have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (\<tau> (add (x, y) (x', y')), l+l'+1)"
      proof -
        have "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (add (\<tau> (x, y)) (x', y'), l+l'+1)" 
          using proj_add.simps \<open>\<tau> (x,y) \<in> e'_aff\<close> \<open>(x', y') \<in> e'_aff\<close> ds' by auto
        moreover have "add (\<tau> (x, y)) (x', y') = \<tau> (add (x, y) (x', y'))"
          by (metis inversion_invariance_1 nz(1) nz(2) nz(3) nz(4) tau_conv tau_idemp_point)
        ultimately show ?thesis by argo          
      qed  

      have add_closure: "add (x,y) (x',y') \<in> e'_aff"
        using in_aff add_closure ld_nz e_e'_iff unfolding delta_def e'_aff_def by auto

      have add_nz: "fst (add (x,y) (x',y')) \<noteq> 0"
                   "snd (add (x,y) (x',y')) \<noteq> 0"
        using ld_nz unfolding delta_def delta_minus_def   
        apply(simp_all)
        apply(simp_all add: c_eq_1)
        using aaa in_aff ld_nz unfolding e'_aff_def e'_def delta_def delta_minus_def delta_plus_def 
        apply(simp_all add: t_expr nz t_nz divide_simps)
         apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr d_nz) 
        unfolding t_expr[symmetric]
        by algebra+

      have class_eq: "gluing `` {(add (x, y) (x', y'), l + l')} =
            {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}" 
        using  add_nz add_closure gluing_class_2 by auto
      have class_proj: "gluing `` {(add (x, y) (x', y'), l + l')} \<in> e_proj"
        using add_closure e_proj_aff by auto

      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
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
            "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1" by blast
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
                aaa ld_nz unfolding e'_aff_0_def by force
        qed
      qed

      show "proj_addition ?p ?q = gluing `` {(add (x, y) (x', y'), l + l')}"
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
        using proj_add.simps \<open>(x,y) \<in> e'_aff\<close> \<open>(\<tau> (x', y')) \<in> e'_aff\<close> by simp
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
            
      have add_closure: "ext_add (x, y) (\<tau> (x', y')) \<in> e'_aff"
      proof -
        obtain x1 y1 where z2_d: "\<tau> (x', y') = (x1,y1)" by fastforce
        define z3 where "z3 = ext_add (x,y) (x1,y1)"
        obtain x2 y2 where z3_d: "z3 = (x2,y2)" by fastforce
        have d': "delta' x y x1 y1 \<noteq> 0"
          using bbb z2_d by auto
        have "(x1,y1) \<in> e'_aff"
          unfolding z2_d[symmetric]
          using \<open>\<tau> (x', y') \<in> e'_aff\<close> by auto
        have e_eq: "e' x y = 0" "e' x1 y1 = 0"
          using \<open>(x,y) \<in> e'_aff\<close> \<open>(x1,y1) \<in> e'_aff\<close> unfolding e'_aff_def by(auto)
          
        have "e' x2 y2 = 0" 
          using z3_d z3_def ext_add_closure[OF d' e_eq, of x2 y2] by blast
        then show ?thesis 
          unfolding e'_aff_def using e_e'_iff z3_d z3_def z2_d by simp
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
            using add_ext_add_2 inversion_invariance_2 assms e_proj_elim_2 in_aff by auto
          then show "add (x, y) (x', y') = \<tau> (ext_add (x, y) (\<tau> (x', y')))" 
            using tau_idemp_point[of "add (x, y) (x', y')"] by argo 
        qed
        
      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
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
            "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1" by blast
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
            using v1 ld_nz in_aff unfolding e'_aff_0_def apply force
            thm trans_add
            apply(subst (asm) trans_add)
            using v3 bbb in_aff taus unfolding e'_aff_1_def by force
        qed
      qed

      have ext_eq: "gluing `` {(ext_add (x, y) (\<tau> (x', y')), l + l'+1)} =
            {(ext_add (x, y) (\<tau> (x', y')), l + l'+1), (\<tau> (ext_add (x, y) (\<tau> (x', y'))), l + l')}" 
        using add_nz add_closure gluing_class_2 by auto
      have class_eq: "gluing `` {(add (x, y) (x', y'), l + l')} =
            {(add (x, y) (x', y'), l + l'), (\<tau> (add (x, y) (x', y')), l + l' + 1)}" 
      proof -
        have "gluing `` {(add (x, y) (x', y'), l + l')} =
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
      then have class_proj: "gluing `` {(add (x, y) (x', y'), l + l')} \<in> e_proj"
      proof -
        have "gluing `` {(add (x, y) (x', y'), l + l')} =
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
        using b ccc unfolding e'_aff_0_def 
                                 delta_def delta'_def delta_plus_def delta_minus_def
                                 delta_x_def delta_y_def e'_aff_def e'_def
        apply(simp add: t_nz nz field_simps)
        apply(simp add: c_eq_1)
        by algebra

      have add_closure: "add (x, y) (x', y') \<in> e'_aff"
        using b(1) \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close> add_closure e_e'_iff
        unfolding e'_aff_0_def delta_def e'_aff_def by(simp del: add.simps,blast)
      have class_eq: "gluing `` {(add (x, y) (x', y'), l + l')} = {(add (x, y) (x', y'), l + l')}"
        using add_z add_closure gluing_class_1 by simp
      have class_proj: "gluing `` {(add (x, y) (x', y'), l + l')} \<in> e_proj"
        using add_closure e_proj_aff by simp

      have dom_eq: 
        "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
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
            "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1" by blast
          then have "e = (add (x, y) (x', y'), l + l') " 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                  ld_nz ds ds' ccc
            unfolding e'_aff_0_def e'_aff_1_def by auto
          then show "e \<in> ?c" by blast
        qed
      next
        show "?s \<supseteq> ?c"
        proof 
          fix e
          assume "e \<in> ?c"         
          then have "e = (add (x, y) (x', y'), l + l')" by blast
          then show "e \<in> ?s"
            using v1 ld_nz in_aff unfolding e'_aff_0_def by force
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
      using c assms unfolding e'_aff_1_def e'_aff_0_def by simp
    then show ?thesis by simp
  qed
qed

lemma gluing_add:
  assumes "gluing `` {((x1,y1),l)} \<in> e_proj" "gluing `` {((x2,y2),j)} \<in> e_proj" "delta x1 y1 x2 y2 \<noteq> 0"
  shows "proj_addition (gluing `` {((x1,y1),l)}) (gluing `` {((x2,y2),j)}) = 
         (gluing `` {(add (x1,y1) (x2,y2),l+j)})"
proof -
  have  p_q_expr: "(gluing `` {((x1,y1),l)} = {((x1, y1), l)} \<or> gluing `` {((x1,y1),l)} = {((x1, y1), l), (\<tau> (x1, y1), l + 1)})" 
                  "(gluing `` {((x2,y2),j)} = {((x2, y2), j)} \<or> gluing `` {((x2,y2),j)} = {((x2, y2), j), (\<tau> (x2, y2), j + 1)})"
    using assms(1,2) gluing_cases_explicit by auto
  then consider
           (1) "gluing `` {((x1,y1),l)} = {((x1, y1), l)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j)}" |
           (2) "gluing `` {((x1,y1),l)} = {((x1, y1), l)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" |
           (3) "gluing `` {((x1,y1),l)} = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j)}" |
           (4) "gluing `` {((x1,y1),l)} = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" by argo 
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
          using commutativity by simp
        have "proj_addition (gluing `` {((x2, y2), j)}) (gluing `` {((x1, y1), l)}) =
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
  assumes "gluing `` {((x,y),l)} = {((x, y), l)}" "gluing `` {((x',y'),l')} = {((x', y'), l')}" 
          "gluing `` {((x,y),l)} \<in> e_proj" "gluing `` {((x',y'),l')} \<in> e_proj" "delta' x y x' y' \<noteq> 0"
  shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')}) = (gluing `` {(ext_add (x,y) (x',y'),l+l')})"
proof -
  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have zeros: "x = 0 \<or> y = 0" "x' = 0 \<or> y' = 0"
    using e_proj_elim_1 assms by presburger+
  
  have ds: "delta' x y x' y' = 0" "delta' x y x' y' \<noteq> 0"     
      using delta'_def delta_x_def delta_y_def zeros(1) zeros(2) apply fastforce
      using assms(5) by simp
  consider
    (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
    (b) "((x, y), x', y') \<in> e'_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
    (c) "((x, y), x', y') \<in> e'_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e'_aff_0"
    using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by argo
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
  assumes "gluing `` {((x,y),l)} = {((x, y), l)}" "gluing `` {((x',y'),l')} = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" 
          "gluing `` {((x,y),l)} \<in> e_proj" "gluing `` {((x',y'),l')} \<in> e_proj" "delta' x y x' y' \<noteq> 0"
  shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')}) = (gluing `` {(ext_add (x,y) (x',y'),l+l')})"
proof -
  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using assms e_proj_eq e_proj_aff by blast+
  then have add_in: "ext_add (x, y) (x', y') \<in> e'_aff"
    using ext_add_closure \<open>delta' x y x' y' \<noteq> 0\<close> delta_def e_e'_iff e'_aff_def by auto
  from in_aff have zeros: "x = 0 \<or> y = 0" "x' \<noteq> 0"  "y' \<noteq> 0"
    using e_proj_elim_1 e_proj_elim_2 assms by presburger+
  have e_proj: "gluing `` {((x,y),l)} \<in> e_proj"
               "gluing `` {((x',y'),l')} \<in> e_proj"
               "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj"
    using e_proj_aff in_aff add_in by auto

  consider
      (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
      (b) "((x, y), x', y') \<in> e'_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e'_aff_1" |
      (c) "((x, y), x', y') \<in> e'_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" 
      using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by fast
  then show ?thesis
  proof(cases)
    case a
    then have "False"
      using in_aff zeros unfolding e_circ_def by force
    then show ?thesis by simp
  next
    case b
    have ld_nz: "delta' x y x' y' = 0" 
     using \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close> b
     unfolding e'_aff_1_def by force
    then have "False"
      using assms e_proj_elim_1 in_aff
      unfolding delta_def delta_minus_def delta_plus_def by blast
    then show ?thesis by blast
  next
   case c   
    then have ld_nz: "delta' x y x' y' \<noteq> 0" unfolding e'_aff_1_def by auto    

    have v1: "proj_add ((x, y), l) ((x', y'), l') = (ext_add (x, y) (x', y'), l + l')"
      by(simp add: \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>  ld_nz del: add.simps)

    have ecirc: "(x',y') \<in> e_circ" "x' \<noteq> 0" "y' \<noteq> 0"
      unfolding e_circ_def using zeros \<open>(x',y') \<in> e'_aff\<close> by blast+
    then have "\<tau> (x', y') \<in> e_circ" 
      using zeros \<tau>_circ by blast
    then have in_aff': "\<tau> (x', y') \<in> e'_aff"
      unfolding e_circ_def by force

    have add_nz: "fst (ext_add (x, y) (x', y')) \<noteq> 0" 
                 "snd (ext_add (x, y) (x', y')) \<noteq> 0" 
      using zeros ld_nz in_aff
      unfolding delta_def delta_plus_def delta_minus_def e'_aff_def e'_def
      apply(simp_all)
      by auto

    have add_in: "ext_add (x, y) (x', y') \<in> e'_aff"
      using ext_add_closure in_aff e_e'_iff ld_nz unfolding e'_aff_def delta_def by simp

    have ld_nz': "delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
      using ld_nz
      unfolding delta'_def delta_x_def delta_y_def
      using zeros by(auto simp add: divide_simps t_nz) 
    
    have tau_conv: "\<tau> (ext_add (x, y) (x', y')) = ext_add (x, y) (\<tau> (x', y'))"
      using zeros e'_aff_x0[OF _ in_aff(1)] e'_aff_y0[OF _ in_aff(1)] 
      apply(simp_all)
      apply(simp_all add: c_eq_1 divide_simps d_nz t_nz)
      apply(elim disjE) 
      apply(simp_all add: t_nz zeros) 
      by auto

    have v2: "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (ext_add (x, y) (x', y')), l+l'+1)"
      using proj_add.simps \<open>\<tau> (x', y') \<in> e'_aff\<close> in_aff tau_conv 
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
       \<in> e'_aff_0 \<union> {((x1, y1), x2, y2). (x1, y1) \<in> e'_aff \<and> (x2, y2) \<in> e'_aff \<and> delta' x1 y1 x2 y2 \<noteq> 0}} =
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
       unfolding assms(1,2) gl_class e'_aff_1_def
       apply(subst eq)
       apply(subst eq_class_simp)
       using gl_class by auto
   qed
  qed    
qed    


lemma gluing_ext_add_4:
 assumes "gluing `` {((x,y),l)} = {((x, y), l), (\<tau> (x, y), l + 1)}" "gluing `` {((x',y'),l')} = {((x', y'), l'), (\<tau> (x', y'), l' + 1)}" 
          "gluing `` {((x,y),l)} \<in> e_proj" "gluing `` {((x',y'),l')} \<in> e_proj" "delta' x y x' y' \<noteq> 0"
  shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')}) = (gluing `` {(ext_add (x,y) (x',y'),l+l')})"
 (is "proj_addition ?p ?q = _")
proof -
  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff"
    using e_proj_aff assms by meson+
  then have nz: "x \<noteq> 0" "y \<noteq> 0" "x' \<noteq> 0" "y' \<noteq> 0" 
    using assms e_proj_elim_2 by auto
  then have circ: "(x,y) \<in> e_circ" "(x',y') \<in> e_circ"
    using in_aff e_circ_def nz by auto
  then have taus: "(\<tau> (x', y')) \<in> e'_aff" "(\<tau> (x, y)) \<in> e'_aff" "\<tau> (x', y') \<in> e_circ"
    using \<tau>_circ circ_to_aff by auto

  consider 
   (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (b) "((x, y), x', y') \<in> e'_aff_0" "((x, y), x', y') \<notin> e'_aff_1" 
   | (c) "((x, y), x', y') \<in> e'_aff_1" 
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
      using b assms unfolding e'_aff_1_def e'_aff_0_def by simp
    then show ?thesis by simp
  next
    case c
    then have ld_nz: "delta' x y x' y' \<noteq> 0" 
      unfolding e'_aff_1_def by auto    
    then have ds: "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) (fst (\<tau> (x', y'))) (snd (\<tau> (x', y'))) \<noteq> 0" 
      unfolding delta'_def delta_x_def delta_y_def 
      (*TODO: note how field_simps is preferable over divide_simps in the field generalization*)
      by(simp add: t_nz field_simps nz)
      
    have v1: "proj_add ((x, y), l) ((x', y'), l') = (ext_add (x, y) (x', y'), l + l')"
      using ld_nz proj_add.simps \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close> by simp
    have v2: "proj_add (\<tau> (x, y), l+1) (\<tau> (x', y'), l'+1) = (ext_add (x, y) (x', y'), l + l')"
      apply(subst proj_add.simps(2)[OF ds,simplified prod.collapse taus(2) taus(1)])
       apply simp
      apply(simp del: ext_add.simps \<tau>.simps)
      apply(rule inversion_invariance_2[OF nz(1,2), of "fst (\<tau> (x',y'))" "snd (\<tau> (x',y'))",
                                 simplified prod.collapse tau_idemp_point])
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
        unfolding e'_aff_def e'_def delta'_def delta_x_def delta_y_def 
        apply(safe)
         apply(simp_all add: divide_simps t_nz nz)
        by algebra+
      
      have v3: 
        "proj_add ((x, y), l) (\<tau> (x', y'), l' + 1) = (\<tau> (ext_add (x, y) (x', y')), l+l'+1)" 
        using proj_add.simps \<open>(\<tau> (x', y')) \<in> e'_aff\<close> 
        apply(simp del: ext_add.simps \<tau>.simps)
        using tau_conv tau_idemp_explicit 
              proj_add.simps(2)[OF aaa \<open>(x,y) \<in> e'_aff\<close>,simplified prod.collapse,OF \<open>(\<tau> (x', y')) \<in> e'_aff\<close>] 
        by (metis (no_types, lifting) add.assoc prod.collapse)

      have ds': "delta' (fst (\<tau> (x, y))) (snd (\<tau> (x, y))) x' y' \<noteq> 0"
        using aaa unfolding delta'_def delta_x_def delta_y_def
        by(simp add: divide_simps t_nz nz algebra_simps power2_eq_square[symmetric] t_expr d_nz)

      have v4: "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (\<tau> (ext_add (x, y) (x', y')), l+l'+1)"
      proof -
        have "proj_add (\<tau> (x, y), l+1) ((x', y'), l') = (ext_add (\<tau> (x, y)) (x', y'), l+l'+1)" 
          using proj_add.simps \<open>\<tau> (x,y) \<in> e'_aff\<close> \<open>(x', y') \<in> e'_aff\<close> ds' by auto
        moreover have "ext_add (\<tau> (x, y)) (x', y') = \<tau> (ext_add (x, y) (x', y'))"
          by (metis inversion_invariance_2 nz tau_conv tau_idemp_point)
        ultimately show ?thesis by argo          
      qed  

      have add_closure: "ext_add (x,y) (x',y') \<in> e'_aff"
        using in_aff ext_add_closure ld_nz e_e'_iff unfolding delta'_def e'_aff_def by auto

      have add_nz: "fst (ext_add (x,y) (x',y')) \<noteq> 0"
                   "snd (ext_add (x,y) (x',y')) \<noteq> 0"
        using ld_nz unfolding delta_def delta_minus_def   
        apply(simp_all)
        using aaa in_aff ld_nz unfolding e'_aff_def e'_def delta'_def delta_x_def delta_y_def 
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
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
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
            "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1" by blast
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
                aaa ld_nz unfolding e'_aff_1_def by force
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
        using proj_add.simps \<open>(x,y) \<in> e'_aff\<close> \<open>(\<tau> (x', y')) \<in> e'_aff\<close> by simp
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
            
      have add_closure: "add (x, y) (\<tau> (x', y')) \<in> e'_aff"
      proof -
        obtain x1 y1 where z2_d: "\<tau> (x', y') = (x1,y1)" by fastforce
        define z3 where "z3 = add (x,y) (x1,y1)"
        obtain x2 y2 where z3_d: "z3 = (x2,y2)" by fastforce
        have d': "delta x y x1 y1 \<noteq> 0"
          using bbb z2_d by auto
        have "(x1,y1) \<in> e'_aff"
          unfolding z2_d[symmetric]
          using \<open>\<tau> (x', y') \<in> e'_aff\<close> by auto
        have e_eq: "e' x y = 0" "e' x1 y1 = 0"
          using \<open>(x,y) \<in> e'_aff\<close> \<open>(x1,y1) \<in> e'_aff\<close> unfolding e'_aff_def by(auto)
          
        have "e' x2 y2 = 0" 
          using d' add_closure[OF z3_d z3_def] e_e'_iff e_eq unfolding delta_def by auto
        then show ?thesis 
          unfolding e'_aff_def using e_e'_iff z3_d z3_def z2_d by simp
      qed     

      have add_nz: "fst(add (x, y) (\<tau> (x', y'))) \<noteq> 0"    
                   "snd(add (x, y) (\<tau> (x', y'))) \<noteq> 0"
        apply(simp_all add: algebra_simps power2_eq_square[symmetric] t_expr)
        apply(simp_all add: divide_simps d_nz t_nz nz c_eq_1)
         apply(safe)
        using bbb ld_nz unfolding delta'_def delta_x_def delta_y_def
                            delta_def delta_plus_def delta_minus_def 
        by(simp_all add: divide_simps t_nz nz algebra_simps 
                              power2_eq_square[symmetric] t_expr d_nz)

           
        have trans_add: "\<tau> (ext_add (x, y) (x', y')) = (add (x, y) (\<tau> (x', y')))" 
                        "ext_add (x, y) (x', y') = \<tau> (add (x, y) (\<tau> (x', y')))" 
        proof -
          show "\<tau> (ext_add (x, y) (x', y')) = (add (x, y) (\<tau> (x', y')))" 
            using inversion_invariance_1 assms add_ext_add nz tau_idemp_point by presburger
          then show "ext_add (x, y) (x', y') = \<tau> (add (x, y) (\<tau> (x', y')))"  
            using tau_idemp_point[of "ext_add (x, y) (x', y')"] by argo
        qed
        
      have dom_eq: "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
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
            "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1" by blast
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
            using v1 ld_nz in_aff unfolding e'_aff_1_def apply force
            apply(subst (asm) trans_add)
            using v3 bbb in_aff taus unfolding e'_aff_0_def by force
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
        using c ccc ld_nz unfolding e'_aff_0_def
                                 delta_def delta'_def delta_plus_def delta_minus_def
                                 delta_x_def delta_y_def e'_aff_def e'_def
        apply(simp_all add: field_simps t_nz nz)
        unfolding t_expr[symmetric] power2_eq_square 
        apply(simp_all add: divide_simps d_nz t_nz) 
        by algebra

      have add_closure: "ext_add (x, y) (x', y') \<in> e'_aff"
        using c(1) \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close> ext_add_closure e_e'_iff
        unfolding e'_aff_1_def delta_def e'_aff_def by simp
      have class_eq: "gluing `` {(ext_add (x, y) (x', y'), l + l')} = {(ext_add (x, y) (x', y'), l + l')}"
        using add_z add_closure gluing_class_1 by simp
      have class_proj: "gluing `` {(ext_add (x, y) (x', y'), l + l')} \<in> e_proj"
        using add_closure e_proj_aff by simp

      have dom_eq: 
        "{proj_add ((x1, y1), i) ((x2, y2), j) |x1 y1 i x2 y2 j.
       ((x1, y1), i) \<in> {((x, y), l), (\<tau> (x, y), l + 1)} \<and>
       ((x2, y2), j) \<in> {((x', y'), l'), (\<tau> (x', y'), l' + 1)} \<and> ((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1} = 
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
            "((x1, y1), x2, y2) \<in> e'_aff_0 \<union> e'_aff_1" by blast
          then have "e = (ext_add (x, y) (x', y'), l + l') " 
            using v1 v2 v3 v4 in_aff taus(1,2) 
                  ld_nz ds ds' ccc
            unfolding e'_aff_0_def e'_aff_1_def 
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
            using v1 ld_nz in_aff unfolding e'_aff_1_def by force
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
  assumes "gluing `` {((x1,y1),l)} \<in> e_proj" "gluing `` {((x2,y2),j)} \<in> e_proj" "delta' x1 y1 x2 y2 \<noteq> 0"
  shows "proj_addition (gluing `` {((x1,y1),l)}) (gluing `` {((x2,y2),j)}) = 
         (gluing `` {(ext_add (x1,y1) (x2,y2),l+j)})"
proof -
  have  p_q_expr: "(gluing `` {((x1,y1),l)} = {((x1, y1), l)} \<or> gluing `` {((x1,y1),l)} = {((x1, y1), l), (\<tau> (x1, y1), l + 1)})" 
                  "(gluing `` {((x2,y2),j)} = {((x2, y2), j)} \<or> gluing `` {((x2,y2),j)} = {((x2, y2), j), (\<tau> (x2, y2), j + 1)})"
    using assms(1,2) gluing_cases_explicit by auto
  then consider
           (1) "gluing `` {((x1,y1),l)} = {((x1, y1), l)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j)}" |
           (2) "gluing `` {((x1,y1),l)} = {((x1, y1), l)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" |
           (3) "gluing `` {((x1,y1),l)} = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j)}" |
           (4) "gluing `` {((x1,y1),l)} = {((x1, y1), l), (\<tau> (x1, y1), l + 1)}" "gluing `` {((x2,y2),j)} = {((x2, y2), j), (\<tau> (x2, y2), j + 1)}" by argo 
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
        have "proj_addition (gluing `` {((x1, y1), l)}) (gluing `` {((x2, y2), j)}) = 
              proj_addition (gluing `` {((x2, y2), j)}) (gluing `` {((x1, y1), l)})"
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

subsubsection \<open>Basic properties\<close>

theorem well_defined:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "proj_addition p q \<in> e_proj"
proof -
  obtain x y l x' y' l'
    where p_q_expr: "p = gluing `` {((x,y),l)}"
                    "q = gluing `` {((x',y'),l')}"
    using e_proj_def assms
    apply(simp)
    apply(elim quotientE)
    by force
  then have in_aff: "(x,y) \<in> e'_aff" 
                    "(x',y') \<in> e'_aff" 
    using e_proj_aff assms by auto

  consider 
   (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (b) "((x, y), x', y') \<in> e'_aff_0" 
         "((x, y), x', y') \<notin> e'_aff_1" 
         "(x, y) \<notin> e_circ \<or> \<not> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" 
   | (c) "((x, y), x', y') \<in> e'_aff_1" 
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
    have taus: "\<tau> (x',y') \<in> e'_aff"
      using in_aff(2) e_circ_def nz(3,4) \<tau>_circ by force
    then have proj: "gluing `` {(\<tau> (x', y'), l'+1)} \<in> e_proj"
                    "gluing `` {((x, y), l)} \<in> e_proj"
      using e_proj_aff in_aff by auto

    have alt_ds: "delta x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0 \<or>
                  delta' x y (fst (\<tau> (x',y'))) (snd (\<tau> (x',y'))) \<noteq> 0"
      (is "?d1 \<noteq> 0 \<or> ?d2 \<noteq> 0")
      using covering_with_deltas ds assms p_q_expr by blast

    have "proj_addition p q = proj_addition (gluing `` {((x, y), l)}) (gluing `` {((x', y'), l')})"
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
        "?d1 \<noteq> 0 \<Longrightarrow> add (x, y) (\<tau> (x', y')) \<in> e'_aff"
        "?d2 \<noteq> 0 \<Longrightarrow> ext_add (x, y) (\<tau> (x', y')) \<in> e'_aff"
      using e_proj_aff add_closure in_aff taus delta_def e'_aff_def e_e'_iff 
       apply fastforce
      using e_proj_aff ext_add_closure in_aff taus delta_def e'_aff_def e_e'_iff
       by fastforce
      
    have f_proj: "?d1 \<noteq> 0 \<Longrightarrow> gluing `` {(add (x, y) (\<tau> (x', y')), l+l'+1)} \<in> e_proj"
                 "?d2 \<noteq> 0 \<Longrightarrow> gluing `` {(ext_add (x, y) (\<tau> (x', y')), l+l'+1)} \<in> e_proj"
      using e_proj_aff closures by force+
      
    then show ?thesis
      using eqs alt_ds by auto
  next
    case b
    then have ds: "delta x y x' y' \<noteq> 0"
      unfolding e'_aff_0_def by auto

    have eq: "proj_addition p q = gluing `` {(add (x, y) (x',y'), l+l')}" 
      (is "?lhs = ?rhs")
      unfolding p_q_expr
      using gluing_add assms p_q_expr ds by meson
    have add_in: "add (x, y) (x',y') \<in> e'_aff"
        using add_closure in_aff ds e_e'_iff 
        unfolding delta_def e'_aff_def by auto
    then show ?thesis
      using eq e_proj_aff by auto  
  next
    case c
    then have ds: "delta' x y x' y' \<noteq> 0"
      unfolding e'_aff_1_def by auto

    have eq: "proj_addition p q = gluing `` {(ext_add (x, y) (x',y'), l+l')}" 
      (is "?lhs = ?rhs")
      unfolding p_q_expr
      using gluing_ext_add assms p_q_expr ds by meson
    have add_in: "ext_add (x, y) (x',y') \<in> e'_aff"
        using ext_add_closure in_aff ds e_e'_iff 
        unfolding delta_def e'_aff_def by auto
    then show ?thesis
      using eq e_proj_aff by auto  
  qed
qed

lemma proj_add_class_inv:
  assumes "gluing `` {((x,y),l)}  \<in> e_proj"
  shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {(i (x,y),l')}) = {((1, 0), l+l')}"
        "gluing `` {(i (x,y),l')} \<in> e_proj"  
proof -
  have in_aff: "(x,y) \<in> e'_aff" 
    using assms e_proj_aff by blast
  then have i_aff: "i (x, y) \<in> e'_aff"
    using i_aff by blast
  show i_proj: "gluing `` {(i (x,y),l')} \<in> e_proj"
    using e_proj_aff i_aff by simp

  consider (1) "delta x y x (-y) \<noteq> 0" | (2) "delta' x y x (-y) \<noteq> 0"
    using add_self in_aff by blast
  then show "proj_addition (gluing `` {((x,y),l)}) (gluing `` {(i (x,y),l')}) = {((1, 0), l+l')}"
  proof(cases)
    case 1
    have "add (x,y) (i (x,y)) = (1,0)"
      using "1" delta_def delta_minus_def delta_plus_def in_aff inverse_generalized by auto
    then show ?thesis 
      using "1" assms gluing_add i_proj identity_equiv by auto
  next
    case 2
    have "ext_add (x,y) (i (x,y)) = (1,0)"
      using "2" delta'_def delta_x_def by auto
    then show ?thesis 
      using "2" assms gluing_ext_add i_proj identity_equiv by auto
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
  then have in_aff: "(x0,y0) \<in> e'_aff"
    using e_proj_aff assms by blast

  have "proj_addition {((1, 0), 0)} x = 
        proj_addition (gluing `` {((1, 0), 0)}) (gluing `` {((x0,y0),l0)})"
    using identity_equiv[of 0] x_expr by argo
  also have "... = gluing `` {(add (1,0) (x0,y0),l0)}"
    apply(subst gluing_add)
    using identity_equiv identity_proj apply simp
    using x_expr assms apply simp
    unfolding delta_def delta_plus_def delta_minus_def apply simp
    by simp
  also have "... = gluing `` {((x0,y0),l0)}"
    using inverse_generalized in_aff 
    unfolding e'_aff_def by simp
  also have "... = x" 
    using x_expr by simp
  finally show ?thesis by simp
qed

corollary proj_addition_comm:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj" 
  shows "proj_addition c1 c2 = proj_addition c2 c1"
  using proj_add_class_comm[OF assms]
  unfolding proj_addition_def by auto

section \<open>Group law\<close>

subsection \<open>Class invariance on group operations\<close>

definition tf  where
  "tf g = image (\<lambda> p. (g (fst p), snd p))"

lemma tf_comp:
  "tf g (tf f s) = tf (g \<circ> f) s"
  unfolding tf_def by force

lemma tf_id:
  "tf id s = s"
  unfolding tf_def by fastforce

definition tf' where
  "tf' = image (\<lambda> p. (fst p, (snd p)+1))"

lemma tf_tf'_commute:
  "tf r (tf' p) = tf' (tf r p)"
  unfolding tf'_def tf_def image_def
  by auto

lemma rho_preserv_e_proj:
  assumes "gluing `` {((x, y), l)} \<in> e_proj"
  shows "tf \<rho> (gluing `` {((x, y), l)}) \<in> e_proj"
proof -
  have in_aff: "(x,y) \<in> e'_aff" 
      using assms e_proj_aff by blast
  have rho_aff: "\<rho> (x,y) \<in> e'_aff" 
      using rot_aff[of \<rho>,OF _ in_aff] rotations_def by blast
    
  have eq: "gluing `` {((x, y), l)} = {((x, y), l)} \<or> 
            gluing `` {((x, y), l)} = {((x, y), l), (\<tau> (x, y), l+1)}"
    using assms gluing_cases_explicit by auto
  from eq consider  
    (1) "gluing `` {((x, y), l)} = {((x, y), l)}" | 
    (2) "gluing `` {((x, y), l)} = {((x, y), l), (\<tau> (x, y), l+1)}"
    by fast
  then show "tf \<rho> (gluing `` {((x, y), l)}) \<in> e_proj"
  proof(cases)
    case 1
    have zeros: "x = 0 \<or> y = 0"
      using in_aff e_proj_elim_1 assms e_proj_aff 1 by auto
    show ?thesis 
      unfolding tf_def
      using rho_aff zeros e_proj_elim_1 1 by auto
  next
    case 2
    have zeros: "x \<noteq> 0" "y \<noteq> 0"
      using in_aff e_proj_elim_2 assms e_proj_aff 2 by auto
    show ?thesis 
      unfolding tf_def
      using rho_aff zeros e_proj_elim_2 2 by fastforce
  qed
qed

lemma insert_rho_gluing:
  assumes "gluing `` {((x, y), l)} \<in> e_proj"
  shows "tf \<rho> (gluing `` {((x, y), l)}) = gluing `` {(\<rho> (x, y), l)}"
proof -
  have in_aff: "(x,y) \<in> e'_aff" 
      using assms e_proj_aff by blast
  have rho_aff: "\<rho> (x,y) \<in> e'_aff" 
      using rot_aff[of \<rho>,OF _ in_aff] rotations_def by blast
  
  have eq: "gluing `` {((x, y), l)} = {((x, y), l)} \<or> 
            gluing `` {((x, y), l)} = {((x, y), l), (\<tau> (x, y), l+1)}"
    using assms gluing_cases_explicit by auto
  from eq consider  
    (1) "gluing `` {((x, y), l)} = {((x, y), l)}" | 
    (2) "gluing `` {((x, y), l)} = {((x, y), l), (\<tau> (x, y), l+1)}"
    by fast
  then show "tf \<rho> (gluing `` {((x, y), l)}) = gluing `` {(\<rho> (x, y), l)}"
  proof(cases)
    case 1
    have zeros: "x = 0 \<or> y = 0"
      using in_aff e_proj_elim_1 assms e_proj_aff 1 by auto
    then have "gluing `` {(\<rho> (x, y), l)} = {(\<rho> (x, y), l)}"
      using gluing_class_1[of "fst (\<rho> (x, y))" "snd (\<rho> (x, y))",
                            simplified prod.collapse, 
                           OF _ rho_aff] by fastforce
    then show ?thesis 
      unfolding tf_def image_def 1 by simp
  next
    case 2
    have zeros: "x \<noteq> 0" "y \<noteq> 0"
      using in_aff e_proj_elim_2 assms e_proj_aff 2 by auto
    then have "gluing `` {(\<rho> (x, y), l)} = {(\<rho> (x, y), l), (\<tau> (\<rho> (x, y)), l+1)}"
      using gluing_class_2[of "fst (\<rho> (x, y))" "snd (\<rho> (x, y))",
                            simplified prod.collapse, OF _ _ rho_aff] by force
    then show ?thesis 
      unfolding tf_def image_def 2 by force
  qed
qed

lemma rotation_preserv_e_proj:
  assumes "gluing `` {((x, y), l)} \<in> e_proj" "r \<in> rotations"
  shows "tf r (gluing `` {((x, y), l)}) \<in> e_proj"
  (is "tf ?r ?g \<in> _")
  using assms
  unfolding rotations_def
  apply(safe)
  using tf_id[of ?g] apply simp
  using rho_preserv_e_proj apply simp
  using tf_comp rho_preserv_e_proj insert_rho_gluing 
  by(metis (no_types, hide_lams) prod.collapse)+

lemma insert_rotation_gluing:
  assumes "gluing `` {((x, y), l)} \<in> e_proj" "r \<in> rotations"
  shows "tf r (gluing `` {((x, y), l)}) = gluing `` {(r (x, y), l)}"
proof -
  have in_proj: "gluing `` {(\<rho> (x, y), l)} \<in> e_proj" "gluing `` {((\<rho> \<circ> \<rho>) (x, y), l)} \<in> e_proj"
      using rho_preserv_e_proj assms insert_rho_gluing by auto+

  consider (1) "r = id" | 
           (2) "r = \<rho>" | 
           (3) "r = \<rho> \<circ> \<rho>" | 
           (4) "r = \<rho> \<circ> \<rho> \<circ> \<rho>" 
    using assms(2) unfolding rotations_def by fast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using tf_id by auto
  next
    case 2
    then show ?thesis using insert_rho_gluing assms by presburger 
  next
    case 3    
    then show ?thesis 
      using insert_rho_gluing assms tf_comp in_proj(1) 
      by (metis (no_types, lifting) \<rho>.simps comp_apply)
  next
    case 4
    then show ?thesis 
      using insert_rho_gluing assms tf_comp in_proj 
      by (metis (no_types, lifting) \<rho>.simps comp_apply)
  qed
qed

lemma tf_tau:
  assumes "gluing `` {((x,y),l)} \<in> e_proj" 
  shows "gluing `` {((x,y),l+1)} = tf' (gluing `` {((x,y),l)})"
  using assms unfolding symmetries_def
proof -
  have in_aff: "(x,y) \<in> e'_aff" 
    using e_proj_aff assms by simp

  have gl_expr: "gluing `` {((x,y),l)} = {((x,y),l)} \<or> 
                 gluing `` {((x,y),l)} = {((x,y),l),(\<tau> (x,y),l+1)}"
    using assms(1) gluing_cases_explicit by simp

  consider (1) "gluing `` {((x,y),l)} = {((x,y),l)}" | 
           (2) "gluing `` {((x,y),l)} = {((x,y),l),(\<tau> (x,y),l+1)}" 
    using gl_expr by argo
  then show "gluing `` {((x,y), l+1)} = tf' (gluing `` {((x,y), l)})"
  proof(cases)
    case 1   
    then have zeros: "x = 0 \<or> y = 0"
      using e_proj_elim_1 in_aff assms by auto
    show ?thesis 
      apply(simp add: 1 tf'_def del: \<tau>.simps)
      using gluing_class_1 zeros in_aff by auto
  next
    case 2
    then have zeros: "x \<noteq> 0" "y \<noteq> 0" 
      using assms e_proj_elim_2 in_aff by auto
    show ?thesis 
      apply(simp add: 2 tf'_def del: \<tau>.simps)
      using gluing_class_2 zeros in_aff by auto
  qed
qed

lemma tf_preserv_e_proj:
  assumes "gluing `` {((x,y),l)} \<in> e_proj" 
  shows "tf' (gluing `` {((x,y),l)}) \<in> e_proj"
  using assms tf_tau[OF assms] 
        e_proj_aff[of x y l] e_proj_aff[of x y "l+1"] by auto  

lemma remove_rho:
  assumes "gluing `` {((x,y),l)} \<in> e_proj"
  shows "gluing `` {(\<rho> (x,y),l)} = tf \<rho> (gluing `` {((x,y),l)})"
  using assms unfolding symmetries_def
proof -
  have in_aff: "(x,y) \<in> e'_aff" using assms e_proj_aff by simp
  have rho_aff: "\<rho> (x,y) \<in> e'_aff"
    using in_aff unfolding e'_aff_def e'_def by(simp,algebra)

  consider (1) "gluing `` {((x,y),l)} = {((x,y),l)}" | 
           (2) "gluing `` {((x,y),l)} = {((x,y),l),(\<tau> (x,y),l+1)}" 
    using assms gluing_cases_explicit by blast
  then show "gluing `` {(\<rho> (x,y), l)} = tf \<rho> (gluing `` {((x,y), l)})" 
  proof(cases)
    case 1
    then have zeros: "x = 0 \<or> y = 0"
      using assms e_proj_elim_1 in_aff by simp
    then have rho_zeros: "fst (\<rho> (x,y)) = 0 \<or> snd (\<rho> (x,y)) = 0" 
      by force   
    have gl_eq: "gluing `` {(\<rho> (x, y), l)} = {(\<rho> (x, y), l)}"
      using gluing_class_1 rho_zeros rho_aff by force
    show ?thesis 
      unfolding gl_eq 1
      unfolding tf_def image_def
      by simp
  next
    case 2
    then have zeros: "x \<noteq> 0" "y \<noteq> 0" 
      using assms e_proj_elim_2 in_aff by auto
    then have rho_zeros: "fst (\<rho> (x,y)) \<noteq> 0" "snd (\<rho> (x,y)) \<noteq> 0" 
      using t_nz by auto
    have gl_eqs: "gluing `` {(\<rho> (x, y), l)} = {(\<rho> (x, y), l), (\<tau> (\<rho> (x, y)), l+1)}"
      using gluing_class_2 rho_zeros rho_aff by force
    show ?thesis 
      unfolding gl_eqs 2
      unfolding tf_def image_def 
      by force
  qed
qed

lemma remove_rotations:
  assumes "gluing `` {((x,y),l)} \<in> e_proj" "r \<in> rotations"
  shows "gluing `` {(r (x,y),l)} = tf r (gluing `` {((x,y),l)})"
proof -
  consider (1) "r = id" | 
           (2) "r = \<rho>" | 
           (3) "r = \<rho> \<circ> \<rho>" | 
           (4) "r = \<rho> \<circ> \<rho> \<circ> \<rho>" 
    using assms(2) unfolding rotations_def by fast
  then show ?thesis
  proof(cases)
    case 1
    then show ?thesis using tf_id by fastforce 
  next
    case 2
    then show ?thesis using remove_rho[OF assms(1)] by fast 
  next
    case 3
    then show ?thesis 
      using remove_rho rho_preserv_e_proj assms(1) 
      by (simp add: tf_comp)
  next
    case 4
    then show ?thesis 
      using remove_rho rho_preserv_e_proj assms(1) 
      by (metis (no_types, lifting) \<rho>.simps comp_apply tf_comp)
  qed
qed

lemma remove_tau:
  assumes "gluing `` {((x,y),l)} \<in> e_proj" "gluing `` {(\<tau> (x,y),l)} \<in> e_proj"
  shows "gluing `` {(\<tau> (x,y),l)} = tf' (gluing `` {((x,y),l)})"
  (is "?gt = tf' ?g")
proof -
  have in_aff: "(x,y) \<in> e'_aff" "\<tau> (x,y) \<in> e'_aff" 
    using assms e_proj_aff by simp+

  consider (1) "?gt = {(\<tau> (x,y),l)}" | (2) "?gt = {(\<tau> (x,y),l),((x,y),l+1)}"
    using tau_idemp_point gluing_cases_points[OF assms(2), of "\<tau> (x,y)" l] by presburger 
  then show ?thesis
  proof(cases)
    case 1
    then have zeros: "x = 0 \<or> y = 0"
      using e_proj_elim_1 in_aff assms by(simp add: t_nz) 
    have "False"
      using zeros in_aff t_n1 d_n1 
      unfolding e'_aff_def e'_def 
      apply(simp)
      apply(safe)
      apply(simp_all add: power2_eq_square algebra_simps)
      apply(simp_all add: power2_eq_square[symmetric] t_expr)
      by algebra+
    then show ?thesis by simp
  next
    case 2
    then have zeros: "x \<noteq> 0" "y \<noteq> 0"
      using e_proj_elim_2 in_aff assms gluing_class_1 by auto
    then have gl_eq: "gluing `` {((x,y),l)} = {((x,y),l),(\<tau> (x,y),l+1)}"
      using in_aff gluing_class_2 by auto
    then show ?thesis 
      by(simp add: 2 gl_eq tf'_def del: \<tau>.simps,fast) 
  qed
qed

lemma remove_add_rho:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "proj_addition (tf \<rho> p) q = tf \<rho> (proj_addition p q)"
proof -
  obtain x y l x' y' l' where 
    p_q_expr: "p = gluing `` {((x, y), l)}" 
              "q = gluing `` {((x', y'), l')}"
    using assms
    unfolding e_proj_def
    apply(elim quotientE)
    by force
  have e_proj:
    "gluing `` {((x, y), l)} \<in> e_proj" 
    "gluing `` {((x', y'), l')} \<in> e_proj"
    using p_q_expr assms by auto
  then have rho_e_proj: 
    "gluing `` {(\<rho> (x, y), l)} \<in> e_proj"
    using remove_rho rho_preserv_e_proj by auto

  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using assms p_q_expr e_proj_aff by auto

  consider
    (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
    (b) "((x, y), x', y') \<in> e'_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
    (c) "((x, y), x', y') \<in> e'_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e'_aff_0"
    using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by argo
  then show ?thesis
  proof(cases)
    case a
    then have e_circ: "(x,y) \<in> e_circ" by auto 
    then have zeros: "x \<noteq> 0" "y \<noteq> 0" unfolding e_circ_def by auto
    from a obtain g where g_expr: 
      "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" by blast
    then obtain r where r_expr: "(x', y') = (\<tau> \<circ> r \<circ> i) (x, y)" "r \<in> rotations"
      using sym_decomp by blast
    have ds: "delta x y x' y' = 0" "delta' x y x' y' = 0" 
      using wd_d_nz[OF g_expr e_circ] wd_d'_nz[OF g_expr e_circ] by auto
 
    have ds'': "delta x y (fst ((r \<circ> i) (x, y))) (snd ((r \<circ> i) (x, y))) \<noteq> 0 \<or> 
                delta' x y (fst ((r \<circ> i) (x, y))) (snd ((r \<circ> i) (x, y))) \<noteq> 0"
      (is "?ds1 \<noteq> 0 \<or> ?ds2 \<noteq> 0")
      using r_expr covering_with_deltas tau_idemp_point ds 
      by (metis comp_apply e_proj(1) e_proj(2))
      
    have ds''': "delta (fst (\<rho> (x,y))) (snd (\<rho> (x,y))) (fst ((r \<circ> i) (x, y))) (snd ((r \<circ> i) (x, y))) \<noteq> 0 \<or> 
                 delta' (fst (\<rho> (x,y))) (snd (\<rho> (x,y))) (fst ((r \<circ> i) (x, y))) (snd ((r \<circ> i) (x, y))) \<noteq> 0"
      (is "?ds3 \<noteq> 0 \<or> ?ds4 \<noteq> 0")
      using r_expr(2) rotation_invariance_3 rotation_invariance_4 delta_com ds'' 
      by (metis (no_types, hide_lams) add.inverse_inverse delta'_com diff_0 minus_diff_eq)
    have ds:"?ds3 \<noteq> 0 \<Longrightarrow> delta x y x (-y) \<noteq> 0"
            "?ds4 \<noteq> 0 \<Longrightarrow> delta' x y x (-y) \<noteq> 0"
            "?ds1 \<noteq> 0 \<Longrightarrow> delta x y x (-y) \<noteq> 0"
            "?ds2 \<noteq> 0 \<Longrightarrow> delta' x y x (-y) \<noteq> 0"
      using ds'''
      (*TODO: a beatiful command for this*)
      using r_expr
      unfolding delta_def delta_plus_def delta_minus_def
                delta'_def delta_x_def delta_y_def rotations_def
      apply(simp add: zeros two_not_zero)
      apply(elim disjE,safe)
      apply(simp_all add: algebra_simps divide_simps t_nz zeros)
      using eq_neg_iff_add_eq_0 apply force
      using eq_neg_iff_add_eq_0 apply force
      using r_expr unfolding rotations_def
      apply(simp add: zeros two_not_zero)
      apply(elim disjE,safe)
      apply(simp_all add: algebra_simps divide_simps t_nz zeros)
      using r_expr unfolding rotations_def
      apply(simp add: zeros two_not_zero)
      apply(elim disjE,safe)
      apply(simp_all add: algebra_simps divide_simps t_nz zeros)
      apply(simp add: zeros two_not_zero)
      using r_expr unfolding rotations_def
      apply(simp add: zeros two_not_zero)
      apply(elim disjE,safe)
      by(simp_all add: algebra_simps divide_simps t_nz zeros)

    have eq: "gluing `` {((\<tau> \<circ> r \<circ> i) (x, y), l')} = 
                gluing `` {((r \<circ> i) (x, y), l'+1)}"
        apply(subst gluing_inv[of "fst ((r \<circ> i) (x, y))" "snd ((r \<circ> i) (x, y))" "l'+1",
                         simplified prod.collapse])
        using zeros r_expr unfolding rotations_def apply fastforce+
        using i_aff[of "(x,y)",OF in_aff(1)] rot_aff[OF r_expr(2)] apply fastforce 
        by force
    have e_proj': "gluing `` {(\<rho> (x, y), l)} \<in> e_proj"
                  "gluing `` {((r \<circ> i) (x, y), l' + 1)} \<in> e_proj"
        using e_proj(1) insert_rho_gluing rho_preserv_e_proj apply auto[1]
        using e_proj(2) eq r_expr(1) by auto
    {
      assume True: "delta x y x (-y) \<noteq> 0" 
      have 1: "add (\<rho> (x, y)) ((r \<circ> i) (x, y)) = (\<rho> \<circ> r) (1,0)"
        (is "?lhs = ?rhs")
      proof -
        have "?lhs = \<rho> (add (x, y) (r (i (x, y))))" 
          using rho_invariance_1_points o_apply[of r i] by presburger
        also have "... = (\<rho> \<circ> r) (add (x, y) (i (x, y)))"
          using rotation_invariance_1_points[OF 
                 r_expr(2),simplified commutativity] by fastforce
        also have "... = ?rhs"
          using inverse_generalized[OF in_aff(1)] True in_aff 
          unfolding delta_def delta_plus_def delta_minus_def by simp
        finally show ?thesis by auto
      qed
    }
    note add_case = this
    {
      assume us_ds: "delta' x y x (-y) \<noteq> 0" 
      have 2: "ext_add (\<rho> (x, y)) ((r \<circ> i) (x, y)) = (\<rho> \<circ> r) (1,0)"
        (is "?lhs = ?rhs")
      proof -
        have "?lhs = \<rho> (ext_add (x, y) (r (i (x, y))))" 
          using rho_invariance_2_points o_apply[of r i] by presburger
        also have "... = (\<rho> \<circ> r) (ext_add (x, y) (i (x, y)))"
          using rotation_invariance_2_points[OF 
                 r_expr(2),simplified ext_add_comm_points] by force
        also have "... = ?rhs"
          using ext_add_inverse[OF zeros] by argo
        finally show ?thesis by auto
      qed
    }
    note ext_add_case = this

    have simp1: "proj_addition (gluing `` {(\<rho> (x, y), l)})
                               (gluing `` {((r \<circ> i) (x, y), l' + 1)})=
            gluing `` {((\<rho> \<circ> r) (1,0),l+l'+1)}"
        (is "proj_addition ?g1 ?g2 = ?g3")
    proof(cases "?ds3 \<noteq> 0")      
      case True
      then have "delta x y x (-y) \<noteq> 0" using ds by blast
      then have 1: "add (\<rho> (x, y)) ((r \<circ> i) (x, y)) = (\<rho> \<circ> r) (1,0)"
        using add_case by auto
      have "proj_addition ?g1 ?g2 = 
                   gluing `` {(add (\<rho> (x, y)) ((r \<circ> i) (x, y)), l+l'+1)}"
          using gluing_add[of "fst (\<rho> (x, y))" "snd (\<rho> (x, y))" l
                              "fst ((r \<circ> i) (x, y))" "snd ((r \<circ> i) (x, y))" "l'+1", 
                           simplified prod.collapse, OF e_proj' ] True
          by (simp add: add.assoc)
        also have "... = ?g3"
          using 1 by auto
        finally show ?thesis by auto
    next
      case False
      then have "delta' x y x (-y) \<noteq> 0" using ds ds''' by fast
      then have 2: "ext_add (\<rho> (x, y)) ((r \<circ> i) (x, y)) = (\<rho> \<circ> r) (1,0)"
        using ext_add_case by auto
      then have "proj_addition ?g1 ?g2 = 
                   gluing `` {(ext_add (\<rho> (x, y)) ((r \<circ> i) (x, y)), l+l'+1)}"
          using gluing_ext_add[of "fst (\<rho> (x, y))" "snd (\<rho> (x, y))" l
                              "fst ((r \<circ> i) (x, y))" "snd ((r \<circ> i) (x, y))" "l'+1", 
                           simplified prod.collapse, OF e_proj'] False         
          by (metis (no_types, lifting) add.assoc ds''')
        also have "... = ?g3"
          using 2 by auto
        finally show ?thesis by auto
    qed
    
    have e_proj': "gluing `` {((x, y), l)} \<in> e_proj"
                  "gluing `` {((r \<circ> i) (x, y), l' + 1)} \<in> e_proj"
      using e_proj apply auto[1]
      using e_proj(2) eq r_expr(1) by auto
    have simp2: "tf \<rho>
     (proj_addition (gluing `` {((x, y), l)})
       (gluing `` {((r \<circ> i) (x, y), l'+1)})) = 
      gluing `` {((\<rho> \<circ> r) (1,0),l+l'+1)}"
      (is "tf _ (proj_addition ?g1 ?g2) = ?g3")
    proof(cases "?ds1 \<noteq> 0")    
      case True
      then have us_ds: "delta x y x (-y) \<noteq> 0" using ds by blast
      then have 1: "add (x, y) ((r \<circ> i) (x, y)) = r (1,0)"
        using add_case rho_invariance_1[of x y "fst ((r \<circ> i) (x, y))" "snd ((r \<circ> i) (x, y))",
                                        simplified prod.collapse]  
        by (metis comp_apply i_idemp_explicit inverse_rule_2 prod.exhaust_sel)
      have "proj_addition ?g1 ?g2 = 
                   gluing `` {(add (x, y) ((r \<circ> i) (x, y)), l+l'+1)}"
        using gluing_add[of x y l
                            "fst ((r \<circ> i) (x, y))" "snd ((r \<circ> i) (x, y))" "l'+1", 
                         simplified prod.collapse, OF e_proj'] True 
        by (metis (no_types, lifting) is_num_normalize(1))
      also have "... = gluing `` {(r (1, 0), l + l' + 1)}"
        using 1 by presburger
      finally have eq': "proj_addition ?g1 ?g2 = gluing `` {(r (1, 0), l + l' + 1)}"
        by auto
      show ?thesis 
        apply(subst eq')
        apply(subst remove_rho[symmetric, of "fst (r (1,0))" "snd (r (1,0))",
                       simplified prod.collapse])
        using e_proj' eq' well_defined by force+
    next
      case False
      then have us_ds: "delta' x y x (-y) \<noteq> 0" using ds ds'' by argo
      then have 2: "ext_add (x, y) ((r \<circ> i) (x, y)) = r (1,0)"
        using ext_add_comm_points ext_add_inverse r_expr(2) rotation_invariance_2_points zeros by auto
      have "proj_addition ?g1 ?g2 = 
                   gluing `` {(ext_add (x, y) ((r \<circ> i) (x, y)), l+l'+1)}"
        using gluing_ext_add e_proj' False
          by (metis (no_types, lifting) add.assoc ds'' prod.collapse)
      also have "... = gluing `` {(r (1, 0), l + l' + 1)}"
        using "2" by auto      
      finally have eq': "proj_addition ?g1 ?g2 = gluing `` {(r (1, 0), l + l' + 1)}"
        by auto
      then show ?thesis
        apply(subst eq')
        apply(subst remove_rho[symmetric, of "fst (r (1,0))" "snd (r (1,0))",
                       simplified prod.collapse])
        using e_proj' eq' well_defined by force+
    qed
    show ?thesis
      unfolding p_q_expr
      unfolding remove_rho[OF e_proj(1),symmetric] r_expr eq
      unfolding simp1 simp2 by blast
next
  case b
    then have ds: "delta x y x' y' \<noteq> 0"
      unfolding e'_aff_0_def by auto
    have eq1: "proj_addition (tf \<rho> (gluing `` {((x, y), l)}))
                        (gluing `` {((x', y'), l')}) = 
          gluing `` {(add (\<rho> (x,y)) (x', y'), l+l')}"
      apply(subst insert_rho_gluing)
      using e_proj apply simp
      apply(subst gluing_add[of "fst (\<rho> (x,y))" "snd (\<rho> (x,y))" l
                        x' y' l',simplified prod.collapse])
      using rho_e_proj apply simp
      using e_proj apply simp
      using ds unfolding delta_def delta_plus_def delta_minus_def
      apply(simp add: algebra_simps)
      by auto

    have eq2: "tf \<rho>
     (proj_addition (gluing `` {((x, y), l)}) (gluing `` {((x', y'), l')})) =
     gluing `` {(add (\<rho> (x,y)) (x', y'), l+l')}"
      apply(subst gluing_add)
      using e_proj ds apply blast+
      apply(subst rho_invariance_1_points)
      apply(subst insert_rho_gluing[of "fst (add (x, y) (x', y'))" 
                               "snd (add (x, y) (x', y'))" "l+l'",
                            simplified prod.collapse])
      using add_closure_points in_aff ds e_proj_aff apply force
      by auto

    then show ?thesis 
      unfolding p_q_expr
      using eq1 eq2 by auto
  next
    case c
    then have ds: "delta' x y x' y' \<noteq> 0"
      unfolding e'_aff_1_def by auto
    have eq1: "proj_addition (tf \<rho> (gluing `` {((x, y), l)}))
                        (gluing `` {((x', y'), l')}) = 
          gluing `` {(ext_add (\<rho> (x,y)) (x', y'), l+l')}"
      apply(subst insert_rho_gluing)
      using e_proj apply simp
      apply(subst gluing_ext_add[of "fst (\<rho> (x,y))" "snd (\<rho> (x,y))" l
                        x' y' l',simplified prod.collapse])
      using rho_e_proj apply simp
      using e_proj apply simp
      using ds unfolding delta'_def delta_x_def delta_y_def
      apply(simp add: algebra_simps)
      by auto

    have eq2: "tf \<rho>
     (proj_addition (gluing `` {((x, y), l)}) (gluing `` {((x', y'), l')})) =
     gluing `` {(ext_add (\<rho> (x,y)) (x', y'), l+l')}"
      apply(subst gluing_ext_add)
      using e_proj ds apply blast+
      apply(subst rho_invariance_2_points)
      apply(subst insert_rho_gluing[of "fst (ext_add (x, y) (x', y'))" 
                               "snd (ext_add (x, y) (x', y'))" "l+l'",
                            simplified prod.collapse])
      using ext_add_closure in_aff ds e_proj_aff 
      unfolding e'_aff_def 
      by auto

    then show ?thesis 
      unfolding p_q_expr
      using eq1 eq2 by auto
  qed
qed  

lemma remove_add_rotation:
  assumes "p \<in> e_proj" "q \<in> e_proj" "r \<in> rotations"
  shows "proj_addition (tf r p) q = tf r (proj_addition p q)"
proof -
  obtain x y l x' y' l' where p_q_expr: "p = gluing `` {((x, y), l)}" "p = gluing `` {((x', y'), l')}"
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
      using remove_add_rho assms(1,2)  rho_preserv_e_proj insert_rho_gluing 
      by (metis (no_types, lifting) p_q_expr(1) tf_comp)
  next
    case 4
    then show ?thesis 
      unfolding p_q_expr
      using remove_add_rho assms(1,2) rho_preserv_e_proj insert_rho_gluing 
      by (smt \<rho>.simps p_q_expr(1) p_q_expr(2) tf_comp)
  qed
qed

lemma remove_add_tau:
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "proj_addition (tf' p) q = tf' (proj_addition p q)"
proof -
  obtain x y l x' y' l' where 
    p_q_expr: "p = gluing `` {((x, y), l)}" 
              "q = gluing `` {((x', y'), l')}"
    using assms
    unfolding e_proj_def
    apply(elim quotientE)
    by force
  have e_proj:
    "gluing `` {((x, y), s)} \<in> e_proj" 
    "gluing `` {((x', y'), s')} \<in> e_proj" for s s'
    using p_q_expr assms e_proj_aff by auto
  then have i_proj:
    "gluing `` {(i (x, y), l'+1)} \<in> e_proj" 
    using proj_add_class_inv(2) by auto

  have in_aff: "(x,y) \<in> e'_aff" "(x',y') \<in> e'_aff" 
    using assms p_q_expr e_proj_aff by auto

  have other_proj:
    "gluing `` {((x, y), l+1)} \<in> e_proj" 
    using in_aff e_proj_aff by auto

  consider
    (a) "(x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y))" |
    (b) "((x, y), x', y') \<in> e'_aff_0" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" |
    (c) "((x, y), x', y') \<in> e'_aff_1" "\<not> ((x, y) \<in> e_circ \<and> (\<exists>g\<in>symmetries. (x', y') = (g \<circ> i) (x, y)))" "((x, y), x', y') \<notin> e'_aff_0"
    using dichotomy_1[OF \<open>(x,y) \<in> e'_aff\<close> \<open>(x',y') \<in> e'_aff\<close>] by argo
  then show ?thesis
  proof(cases)
    case a
    then have e_circ: "(x,y) \<in> e_circ" by auto 
    then have zeros: "x \<noteq> 0" "y \<noteq> 0" unfolding e_circ_def by auto
    from a obtain g where g_expr: 
      "g \<in> symmetries" "(x', y') = (g \<circ> i) (x, y)" by blast
    then obtain r where r_expr: "(x', y') = (\<tau> \<circ> r \<circ> i) (x, y)" "r \<in> rotations"
      using sym_decomp by blast   
    have eq: "gluing `` {((\<tau> \<circ> r \<circ> i) (x, y),s)} = 
                gluing `` {((r \<circ> i) (x, y), s+1)}" for s
        apply(subst gluing_inv[of "fst ((r \<circ> i) (x, y))" "snd ((r \<circ> i) (x, y))" "s+1",
                         simplified prod.collapse])
        using zeros r_expr unfolding rotations_def apply fastforce+
        using i_aff[of "(x,y)",OF in_aff(1)] rot_aff[OF r_expr(2)] apply fastforce 
        by force

    have "proj_addition (tf' (gluing `` {((x, y), l)}))
                        (gluing `` {((x', y'), l')}) = 
          proj_addition (gluing `` {((x, y), l+1)})
                        (gluing `` {((\<tau> \<circ> r \<circ> i) (x, y), l')})"     
      (is "?lhs = _")
      using assms(1) p_q_expr(1) tf_tau r_expr by auto
    also have "... =
          proj_addition (gluing `` {((x, y), l+1)})
                        (gluing `` {(r (i (x, y)), l'+1)})" 
      using eq by auto
    also have "... =  
          tf r (proj_addition (gluing `` {((x, y), l+1)})
                        (gluing `` {(i (x, y), l'+1)}))"
    proof -
      note lem1 = remove_rotations[of "fst (i (x,y))" "snd (i (x,y))" "l'+1",
               OF _ r_expr(2), simplified prod.collapse, OF i_proj] 
      show ?thesis
      apply(subst lem1)
      apply(subst proj_addition_comm)
        using other_proj apply simp
        using lem1 assms(2) eq p_q_expr(2) r_expr(1) apply auto[1]
        apply(subst remove_add_rotation[OF _ _ r_expr(2)])
        using i_proj other_proj apply(simp,simp)
        apply(subst proj_addition_comm)
        using i_proj other_proj by auto       
    qed
    also have "... = tf r {((1,0),l+l')}"
      (is "_ = ?rhs")
      using proj_add_class_inv(1)[OF other_proj, of "l'+1"] by force
    finally have simp1: "?lhs = ?rhs" 
      by auto

    have "tf' (proj_addition (gluing `` {((x, y), l)})
          (gluing `` {((x', y'), l')})) = 
          tf' (proj_addition (gluing `` {((x, y), l)})
          (gluing `` {((\<tau> \<circ> r \<circ> i) (x, y), l')}))"     
      (is "?lhs = _")
      using assms(1) p_q_expr(1) tf_tau r_expr by auto
    also have "... =
          tf' (proj_addition (gluing `` {((x, y), l)})
          (gluing `` {(r (i (x, y)), l'+1)}))" 
      using eq by auto
    also have "... =  
          tf r {((1, 0), l + l')}"
    proof -
      note lem1 = remove_rotations[of "fst (i (x,y))" "snd (i (x,y))" "l'+1",
               OF _ r_expr(2), simplified prod.collapse, OF i_proj] 
      show ?thesis
      apply(subst lem1)
      apply(subst proj_addition_comm)
        using i_proj e_proj apply(simp,simp)
         apply (simp add: r_expr(2) rotation_preserv_e_proj)          
        apply(subst remove_add_rotation[OF _ _ r_expr(2)])
        using i_proj e_proj apply(simp,simp)
        apply(subst proj_addition_comm)
        using i_proj e_proj apply(simp,simp) 
        apply(subst proj_add_class_inv(1))
        using e_proj apply simp 
        apply(subst tf_tf'_commute[symmetric])
        apply(subst identity_equiv[symmetric])
        apply(subst tf_tau[symmetric])
        apply (simp add: identity_equiv identity_proj)
        apply(subst identity_equiv) 
        by auto 
    qed
    finally have simp2: "?lhs = ?rhs" 
      by auto

    show ?thesis 
      unfolding p_q_expr
      unfolding remove_rho[OF e_proj(1),symmetric] 
      unfolding simp1 simp2 by auto
  next
    case b
    then have ds: "delta x y x' y' \<noteq> 0"
      unfolding e'_aff_0_def by auto
    have add_proj: "gluing `` {(add (x, y) (x', y'), s)} \<in> e_proj" for s
      using e_proj add_closure_points ds e_proj_aff by auto
    show ?thesis
      unfolding p_q_expr 
      apply(subst tf_tau[symmetric],simp add: e_proj)
      apply(subst (1 2) gluing_add,
           (simp add: e_proj ds other_proj add_proj del: add.simps)+)
      apply(subst tf_tau[of "fst (add (x, y) (x', y'))" 
                    "snd (add (x, y) (x', y'))",simplified prod.collapse,symmetric],
            simp add: add_proj del: add.simps)
      by(simp add: algebra_simps)
  next
    case c
    then have ds: "delta' x y x' y' \<noteq> 0"
      unfolding e'_aff_1_def by auto
    have add_proj: "gluing `` {(ext_add (x, y) (x', y'), s)} \<in> e_proj" for s
      using e_proj ext_add_closure_points ds e_proj_aff by auto
    show ?thesis
      unfolding p_q_expr 
      apply(subst tf_tau[symmetric],simp add: e_proj)
      apply(subst (1 2) gluing_ext_add,
           (simp add: e_proj ds other_proj add_proj del: ext_add.simps)+)
      apply(subst tf_tau[of "fst (ext_add (x, y) (x', y'))" 
                    "snd (ext_add (x, y) (x', y'))",simplified prod.collapse,symmetric],
            simp add: add_proj del: ext_add.simps)
      by(simp add: algebra_simps)
  qed
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
    "s = gluing `` {((x, y), l)}"
    by (metis assms e_proj_def prod.collapse quotientE)
  then have "s = {((x, y), l)} \<or> s = {((x, y), l), (\<tau> (x, y), l+1)}"  
    using assms gluing_cases_explicit by auto
  then show ?thesis 
    apply(elim disjE)
    by(simp add: tf'_def)+
qed

definition tf'' where
 "tf'' g s = tf' (tf g s)"

lemma remove_sym:
  assumes "gluing `` {((x, y), l)} \<in> e_proj" "gluing `` {(g (x, y), l)} \<in> e_proj" "g \<in> symmetries"
  shows "gluing `` {(g (x, y), l)} = tf'' (\<tau> \<circ> g) (gluing `` {((x, y), l)})"
  using assms remove_tau remove_rotations sym_decomp
proof -
  obtain r where r_expr: "r \<in> rotations" "g = \<tau> \<circ> r"
    using assms sym_decomp by blast
  then have e_proj: "gluing `` {(r (x, y), l)} \<in> e_proj"
    using rotation_preserv_e_proj insert_rotation_gluing assms by simp
  have "gluing `` {(g (x, y), l)} = gluing `` {(\<tau> (r (x, y)), l)}"
    using r_expr by simp
  also have "... = tf' (gluing `` {(r (x, y), l)})"
    using remove_tau assms e_proj r_expr 
    by (metis calculation prod.collapse)
  also have "... = tf' (tf r (gluing `` {((x, y), l)}))"
    using remove_rotations r_expr assms(1) by force
  also have "... = tf'' (\<tau> \<circ> g) (gluing `` {((x, y), l)})"
    using r_expr(2) tf''_def tau_idemp_explicit 
    by (metis (no_types, lifting) comp_assoc id_comp tau_idemp)
  finally show ?thesis by simp
qed

lemma remove_add_sym:
  assumes "p \<in> e_proj" "q \<in> e_proj" "g \<in> rotations"
  shows "proj_addition (tf'' g p) q = tf'' g (proj_addition p q)"
proof -
  obtain x y l x' y' l' where p_q_expr: "p =  gluing `` {((x, y), l)}" "q =  gluing `` {((x', y'), l')}"
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

  
(* perhaps do this
lemma remove_add_tau_iff: 
  assumes "p \<in> e_proj" "q \<in> e_proj"
  shows "(tf \<tau> p) \<in> e_proj \<longleftrightarrow> tf \<tau> (proj_addition p q) \<in> e_proj"
proof(standard)
  assume "tf \<tau> p \<in> e_proj"

  show "tf \<tau> (proj_addition p q) \<in> e_proj"
qed
*)

lemma tf''_preserv_e_proj:
  assumes "gluing `` {((x,y),l)} \<in> e_proj" "r \<in> rotations"
  shows "tf'' r (gluing `` {((x,y),l)}) \<in> e_proj"
  unfolding tf''_def
  apply(subst insert_rotation_gluing[OF assms])
  using rotation_preserv_e_proj[OF assms] tf_preserv_e_proj insert_rotation_gluing[OF assms] 
  by (metis i.cases)

lemma tf'_injective:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj"
  assumes "tf' (c1) = tf' (c2)"
  shows "c1 = c2"
  using assms by (metis tf'_idemp)
(*
lemma tf_injective:
  assumes "c1 \<in> e_proj" "c2 \<in> e_proj" "r \<in> rotations"
  assumes "tf r c1 = tf r c2"
  shows "c1 = c2"
proof -
  obtain x y l x' y' l' where p_q_expr: 
    "c1 = gluing `` {((x, y), l)}"
    "c2 = gluing `` {((x', y'), l')}"
    using assms
    unfolding e_proj_def
    apply(elim quotientE)
    by auto
  have "tf r c1 = gluing `` {(r (x, y), l)}"
       "tf r c2 = gluing `` {(r (x', y'), l')}"
    using assms insert_rotation_gluing p_q_expr by blast+
  then show ?thesis
    sledgehammer
  then have "s = {((x, y), l)} \<or> s = {((x, y), l), (\<tau> (x, y), l+1)}"  
    using assms gluing_cases_explicit by auto
  then show ?thesis 
    apply(elim disjE)
    by(simp add: tf'_def)+
qed*)

subsection \<open>Associativities\<close>

(* in the appropiate localizations means we can use delta \<noteq> 0 *)
lemma add_add_add_add_assoc:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms unfolding e'_aff_def delta_def apply(simp)
  using associativity e_e'_iff by fastforce

lemma fstI: "x = (y, z) \<Longrightarrow> y = fst x"
  by simp

lemma sndI: "x = (y, z) \<Longrightarrow> z = snd x"
  by simp



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
                          @{cprop "e' x1 y1 = 0"}, @{cprop "e' x2 y2 = 0"}, @{cprop "e' x3 y3 = 0"} 
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
                      @{term "r1 * e' x1 y1 + r2 * e' x2 y2 + r3 * e' x3 y3"})))))

  val gyDeltay = 
    HOLogic.mk_Trueprop(
     HOLogic.mk_exists ("r1",@{typ 'a},
      HOLogic.mk_exists("r2",@{typ 'a},
       HOLogic.mk_exists("r3",@{typ 'a},
        HOLogic.mk_eq(HOLogic.mk_binop "Groups.times_class.times" (sndminus,normalizey), 
                      @{term "r1 * e' x1 y1 + r2 * e' x2 y2 + r3 * e' x3 y3"})))))

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
                      [@{thm c_eq_1},@{thm t_expr(1)},@{thm delta_x_def},
                       @{thm delta_y_def}, @{thm delta_plus_def}, 
                       @{thm delta_minus_def}, @{thm e'_def}]) 1
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
                                [@{thm c_eq_1},@{thm t_expr(1)},@{thm delta_x_def},
                                 @{thm delta_y_def}, @{thm delta_plus_def}, 
                                 @{thm delta_minus_def}, @{thm e'_def}]) 1
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
  TODO: change into 1 2 3 4
*)
local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_ext_ext_assoc"}, []), [concrete_assoc "ext" "ext" "ext" "ext"]) #> snd 
\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_ext_ext_assoc"}, []), [concrete_assoc "add" "ext" "ext" "ext"]) #> snd 
\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_ext_add_assoc"}, []), [concrete_assoc "ext" "ext" "ext" "add"]) #> snd 
\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_add_ext_assoc"}, []), [concrete_assoc "ext" "add" "add" "ext"]) #> snd 
\<close>

lemma add_ext_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
  shows "add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_ext_add_ext_assoc 
  apply(safe) 
  using ext_add.simps by metis

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_ext_ext_assoc"}, []), [concrete_assoc "ext" "add" "ext" "ext"]) #> snd 
\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_add_add_assoc"}, []), [concrete_assoc "ext" "add" "add" "add"]) #> snd 
\<close>

lemma add_ext_add_add_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_ext_add_add_assoc 
  apply(safe) 
  using prod.collapse ext_add.simps by metis

local_setup \<open>
  Local_Theory.note ((@{binding "add_add_ext_add_assoc"}, []), [concrete_assoc "add" "add" "ext" "add"]) #> snd 
\<close>

lemma add_add_ext_add_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta' x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "add (add (x1,y1) (x2,y2)) (x3,y3) = ext_add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_add_ext_add_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "add_add_ext_ext_assoc"}, []), [concrete_assoc "add" "add" "ext" "ext"]) #> snd 
\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "add_add_add_ext_assoc"}, []), [concrete_assoc "add" "add" "add" "ext"]) #> snd 
\<close>

lemma add_add_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using add_add_add_ext_assoc 
  apply(safe) 
  by (metis ext_add.simps prod.collapse)

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_add_ext_assoc"}, []), [concrete_assoc "add" "ext" "add" "ext"]) #> snd 
\<close>

lemma ext_add_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using ext_add_add_ext_assoc 
  apply(safe) 
  using prod.collapse ext_add.simps by metis

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_add_add_assoc"}, []), [concrete_assoc "add" "ext" "add" "add"]) #> snd 
\<close>

lemma ext_add_add_add_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (add (x1,y1) (x2,y2))) (snd (add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: add.simps)
  using ext_add_add_add_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "ext_add_ext_add_assoc"}, []), [concrete_assoc "add" "ext" "ext" "add"]) #> snd 
\<close>

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_add_add_assoc"}, []), [concrete_assoc "ext" "ext" "add" "add"]) #> snd 
\<close>

lemma ext_ext_add_add_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (add (x2,y2) (x3,y3))) (snd (add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using ext_ext_add_add_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "ext_ext_add_ext_assoc"}, []), [concrete_assoc "ext" "ext" "add" "ext"]) #> snd 
\<close>

lemma ext_ext_add_ext_assoc_points:
  assumes "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff"
  assumes "delta' x1 y1 x2 y2 \<noteq> 0" "delta' x2 y2 x3 y3 \<noteq> 0"
          "delta' (fst (ext_add (x1,y1) (x2,y2))) (snd (ext_add (x1,y1) (x2,y2))) x3 y3 \<noteq> 0"
          "delta x1 y1 (fst (ext_add (x2,y2) (x3,y3))) (snd (ext_add (x2,y2) (x3,y3))) \<noteq> 0"
        shows "ext_add (ext_add (x1,y1) (x2,y2)) (x3,y3) = add (x1,y1) (ext_add (x2,y2) (x3,y3))"
  using assms 
  unfolding e'_aff_def delta_def delta'_def
  apply(simp del: ext_add.simps add.simps)
  using ext_ext_add_ext_assoc 
  apply(safe) 
  using prod.collapse by blast

local_setup \<open>
  Local_Theory.note ((@{binding "add_ext_ext_add_assoc"}, []), [concrete_assoc "ext" "add" "ext" "add"]) #> snd 
\<close>

subsection \<open>Lemmas for associativity\<close>

lemma cancellation_assoc:
  assumes "gluing `` {((x1,y1),0)} \<in> e_proj" "gluing `` {((x2,y2),0)} \<in> e_proj" "gluing `` {(i (x2,y2),0)} \<in> e_proj"
  shows "proj_addition (proj_addition (gluing `` {((x1,y1),0)}) (gluing `` {((x2,y2),0)})) (gluing `` {(i (x2,y2),0)}) = 
         gluing `` {((x1,y1),0)}"
  (is "proj_addition (proj_addition ?g1 ?g2) ?g3 = ?g1")
proof -
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "i (x2,y2) \<in> e'_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have one_in: "gluing `` {((1, 0), 0)} \<in> e_proj"
    using identity_proj identity_equiv by auto

  have e_proj: "gluing `` {((x1, y1), 0)} \<in> e_proj"
               "gluing `` {((x2, y2), 0)} \<in> e_proj"
               "gluing `` {(i (x1, y1), 0)} \<in> e_proj"
               "{((1, 0), 0)} \<in> e_proj"
               "gluing `` {(i (x2, y2), 0)} \<in> e_proj"                   
    using e_proj_aff in_aff apply(simp,simp)
    using assms proj_add_class_inv apply blast
    using identity_equiv one_in apply auto[1]
    using assms(2) proj_add_class_inv by blast

  {
    assume "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))" 
    then obtain g where g_expr: "g \<in> symmetries" "(x2, y2) = (g \<circ> i) (x1, y1)" by auto
    then obtain g' where g_expr': "g' \<in> symmetries" "i (x2,y2) = g' (x1, y1)" "g \<circ> g' = id"
      using symmetries_i_inverse[OF g_expr(1), of x1 y1] 
            i_idemp pointfree_idE by force      

    obtain r where r_expr: "r \<in> rotations" "(x2, y2) = (\<tau> \<circ> r) (i (x1, y1))" "g = \<tau> \<circ> r"
      using g_expr sym_decomp by force
            
   have e_proj_comp: 
      "gluing `` {(g (i (x1, y1)), 0)} \<in> e_proj"
      "gluing `` {(g (i (x2, y2)), 0)} \<in> e_proj"
      using assms g_expr apply force
      using assms g_expr' g_expr' pointfree_idE by fastforce

    have g2_eq: "?g2 = tf'' r (gluing `` {(i (x1, y1), 0)})"
      (is "_ = tf'' _ ?g4")
      apply(simp add: r_expr del: i.simps o_apply)
      apply(subst remove_sym[of "fst (i (x1,y1))" "snd (i (x1,y1))" 0 "\<tau> \<circ> r", 
                     simplified prod.collapse],
            (simp add: e_proj e_proj_comp r_expr del: i.simps o_apply)+)
      using e_proj_comp r_expr g_expr apply blast+
      using tau_idemp comp_assoc[of \<tau> \<tau> r,symmetric] 
            id_comp[of r] by presburger
    
    have eq1: "proj_addition (proj_addition ?g1 (tf'' r ?g4)) ?g3 = ?g1"
      apply(subst proj_addition_comm)
      using e_proj g2_eq[symmetric] apply(simp,simp)
      apply(subst remove_add_sym)
      using e_proj r_expr apply(simp,simp,simp)
      apply(subst proj_addition_comm)
      using e_proj apply(simp,simp)
      apply(subst proj_add_class_inv(1))
      using e_proj apply simp
      apply(subst remove_add_sym)
      using e_proj r_expr apply(simp,simp,simp)
      apply(simp del: i.simps)
      apply(subst proj_add_class_identity)
      using e_proj apply simp
      apply(subst remove_sym[symmetric, of "fst (i (x2,y2))" "snd (i (x2,y2))" 0 "\<tau> \<circ> r",
                     simplified prod.collapse comp_assoc[of \<tau> \<tau> r,symmetric]
                                tau_idemp id_o])
      using e_proj apply simp
      using e_proj_comp(2) r_expr(3) apply auto[1]
      using g_expr(1) r_expr(3) apply auto[1]
      using g_expr'(2) g_expr'(3) pointfree_idE r_expr(3) by fastforce
    have ?thesis
      unfolding g2_eq eq1 by auto
  }
  note dichotomy_case = this
  
  consider (1) "x1 \<noteq> 0" "y1 \<noteq> 0" "x2 \<noteq> 0" "y2 \<noteq> 0" | (2) "x1 = 0 \<or> y1 = 0 \<or> x2 = 0 \<or> y2 = 0" by fastforce
  then show ?thesis
  proof(cases)
    case 1
    have taus: "\<tau> (i (x2, y2)) \<in> e'_aff"
    proof -
      have "i (x2,y2) \<in> e_circ"
        using e_circ_def in_aff 1 by auto
      then show ?thesis
        using \<tau>_circ circ_to_aff by blast
    qed
     
    consider
      (a) "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))" |
      (b) "((x1, y1), x2, y2) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1)))" |
      (c) "((x1, y1), x2, y2) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1)))" "((x1, y1), x2, y2) \<notin> e'_aff_0"
        using dichotomy_1 in_aff by blast
    then show ?thesis 
    proof(cases)
      case a 
      then show ?thesis 
        using dichotomy_case by auto
    next
      case b      
      have pd: "delta x1 y1 x2 y2 \<noteq> 0"
        using b(1) unfolding e'_aff_0_def by simp

      have ds: "delta x2 y2 x2 (-y2) \<noteq> 0 \<or> delta' x2 y2 (x2) (-y2) \<noteq> 0 "
        using in_aff d_n1 
        unfolding delta_def delta_plus_def delta_minus_def
                  delta'_def delta_x_def delta_y_def
                  e'_aff_def e'_def
        apply(simp add: t_expr two_not_zero)
        apply(safe)
        apply(simp_all add: algebra_simps) 
        by(simp add: semiring_normalization_rules(18) semiring_normalization_rules(29) two_not_zero)+  

      have eq1: "proj_addition ?g1 ?g2 = gluing `` {(add (x1, y1) (x2, y2), 0)}" 
        (is "_ = ?g_add")
        using gluing_add[OF assms(1,2) pd] by force
      then obtain rx ry where r_expr: 
        "rx = fst (add (x1, y1) (x2, y2))"
        "ry = snd (add (x1, y1) (x2, y2))"
        "(rx,ry) = add (x1,y1) (x2,y2)"
        by simp
      have in_aff_r: "(rx,ry) \<in> e'_aff"
        using in_aff add_closure_points pd r_expr by auto  
      have e_proj_r: "gluing `` {((rx,ry), 0)} \<in> e_proj"
        using e_proj_aff in_aff_r by auto
       
      consider
        (aa) "(rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry))" |
        (bb) "((rx, ry), i (x2, y2)) \<in> e'_aff_0" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry)))" |
        (cc) "((rx, ry), i (x2, y2)) \<in> e'_aff_1" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry)))" "((rx, ry), i (x2, y2)) \<notin> e'_aff_0"        
        using dichotomy_1[OF in_aff_r in_aff(3)] by fast        
      then show ?thesis 
      proof(cases)
        case aa
        then obtain g where g_expr: 
          "g \<in> symmetries" "(i (x2, y2)) = (g \<circ> i) (rx, ry)" by blast
        then obtain r where rot_expr: 
          "r \<in> rotations" "(i (x2, y2)) = (\<tau> \<circ> r \<circ> i) (rx, ry)" "\<tau> \<circ> g = r" 
          using sym_decomp pointfree_idE sym_to_rot tau_idemp by fastforce
       
        have e_proj_sym: "gluing `` {(g (i (rx, ry)), 0)} \<in> e_proj"
                         "gluing `` {(i (rx, ry), 0)} \<in> e_proj"
          using assms(3) g_expr(2) apply force
          using e_proj_r proj_add_class_inv(2) by blast
        
        from aa have pd': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) = 0"
          using wd_d_nz by auto
        consider
          (aaa) "(rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (i (x2, y2)) = (g \<circ> i) (rx, ry))" |
          (bbb) "((rx, ry), \<tau> (i (x2, y2))) \<in> e'_aff_0" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (i (x2, y2)) = (g \<circ> i) (rx, ry)))" |
          (ccc) "((rx, ry), \<tau> (i (x2, y2))) \<in> e'_aff_1" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (i (x2, y2)) = (g \<circ> i) (rx, ry)))" "((rx, ry), \<tau> (i (x2, y2))) \<notin> e'_aff_0"        
          using dichotomy_1[OF in_aff_r taus] by fast
        then show ?thesis 
        proof(cases)
          case aaa 
          have pd'': "delta rx ry (fst (\<tau> (i (x2, y2)))) (snd (\<tau> (i (x2, y2)))) = 0"
            using wd_d_nz aaa by auto
          from aaa obtain g' where g'_expr: 
            "g' \<in> symmetries" "\<tau> (i (x2, y2)) = (g' \<circ> i) (rx, ry)" 
            by blast
          then obtain r' where r'_expr: 
            "r' \<in> rotations" "\<tau> (i (x2, y2)) = (\<tau> \<circ> r' \<circ> i) (rx, ry)" 
            using sym_decomp by blast
          from r'_expr have 
            "i (x2, y2) = (r' \<circ> i) (rx, ry)" 
            using tau_idemp_point by (metis comp_apply)
          from this rot_expr have "(\<tau> \<circ> r \<circ> i) (rx, ry) = (r' \<circ> i) (rx, ry)" 
            by argo
          then obtain ri' where "ri' \<in> rotations" "ri'( (\<tau> \<circ> r \<circ> i) (rx, ry)) = i (rx, ry)"
            by (metis comp_def rho_i_com_inverses(1) r'_expr(1) rot_inv tau_idemp tau_sq)
          then have "(\<tau> \<circ> ri' \<circ> r \<circ> i) (rx, ry) = i (rx, ry)"
            by (metis comp_apply rot_tau_com)
          then obtain g'' where g''_expr: "g'' \<in> symmetries" "g'' (i ((rx, ry))) = i (rx,ry)"
            using \<open>ri' \<in> rotations\<close> rot_expr(1) rot_comp tau_rot_sym by force
          have in_g: "g'' \<in> G"
            using g''_expr(1) unfolding G_def symmetries_def by blast
          have in_circ: "i (rx, ry) \<in> e_circ"
            using aa i_circ by blast
          then have "g'' = id"
            using g_no_fp in_g in_circ g''_expr(2) by blast
          then have "False"
            using sym_not_id sym_decomp  g''_expr(1) by fastforce
          then show ?thesis by simp
        next
          case bbb  
          then have pd': "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
            unfolding e'_aff_0_def by simp          
          then have pd'': "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
            using 1 delta_add_delta'_1 in_aff pd r_expr by auto            
          have "False"
            using aa pd'' wd_d'_nz by auto
          then show ?thesis by auto
        next 
          case ccc 
          then have pd': "delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
            unfolding e'_aff_0_def e'_aff_1_def by auto
          then have pd'': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
            using 1 delta_add_delta'_2 in_aff pd r_expr by auto
          have "False"
            using aa pd'' wd_d_nz by auto      
          then show ?thesis by auto
        qed
      next
        case bb        
        then have pd': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
          using bb unfolding e'_aff_0_def r_expr by simp
        have add_assoc: "add (add (x1, y1) (x2, y2)) (i (x2, y2)) = (x1,y1)"
        proof(cases "delta x2 y2 x2 (-y2) \<noteq> 0")
          case True
          have inv: "add (x2, y2) (i (x2, y2)) = (1,0)"
            using inverse_generalized[OF in_aff(2)] True
            unfolding delta_def delta_minus_def delta_plus_def by auto
          show ?thesis
            apply(subst add_add_add_add_assoc[OF in_aff(1,2), 
                 of "fst (i (x2,y2))" "snd (i (x2,y2))",
                 simplified prod.collapse])  
            using in_aff(3) pd True pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        next
          case False
          then have ds': "delta' x2 y2 x2 (- y2) \<noteq> 0"
            using ds by auto
          have inv: "ext_add (x2, y2) (i (x2, y2)) = (1,0)"
            using ext_add_inverse 1 by simp
          show ?thesis
            apply(subst add_add_add_ext_assoc_points[of x1 y1 x2 y2 
                  "fst (i (x2,y2))" "snd (i (x2,y2))", simplified prod.collapse]) 
            using in_aff pd ds' pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        qed

        show ?thesis
          apply(subst gluing_add,(simp add: e_proj pd del: add.simps i.simps)+)
          apply(subst gluing_add[of rx ry 0 "fst (i (x2,y2))" "snd (i (x2,y2))",
                         simplified r_expr prod.collapse])         
          using e_proj_r r_expr e_proj pd' apply(simp,simp,simp)
          apply(subst add_assoc)
          by auto
      next
        case cc 
        then have pd': "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
          using cc unfolding e'_aff_1_def r_expr by simp
        have add_assoc: "ext_add (add (x1, y1) (x2, y2)) (i (x2, y2)) = (x1,y1)"
        proof(cases "delta x2 y2 x2 (-y2) \<noteq> 0")
          case True
          have inv: "add (x2, y2) (i (x2, y2)) = (1,0)"
            using inverse_generalized[OF in_aff(2)] True
            unfolding delta_def delta_minus_def delta_plus_def by auto
          show ?thesis
            apply(subst ext_add_add_add_assoc_points[OF in_aff(1,2), 
                 of "fst (i (x2,y2))" "snd (i (x2,y2))",
                 simplified prod.collapse])  
            using in_aff(3) pd True pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        next
          case False
          then have ds': "delta' x2 y2 x2 (- y2) \<noteq> 0"
            using ds by auto
          have inv: "ext_add (x2, y2) (i (x2, y2)) = (1,0)"
            using ext_add_inverse 1 by simp
          show ?thesis
            apply(subst ext_add_add_ext_assoc_points[of x1 y1 x2 y2 
                  "fst (i (x2,y2))" "snd (i (x2,y2))", simplified prod.collapse]) 
            using in_aff pd ds' pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        qed

        show ?thesis
          apply(subst gluing_add,(simp add: e_proj pd del: add.simps i.simps)+)
          apply(subst gluing_ext_add[of rx ry 0 "fst (i (x2,y2))" "snd (i (x2,y2))",
                         simplified r_expr prod.collapse])         
          using e_proj_r r_expr e_proj pd' apply(simp,simp,simp)
          apply(subst add_assoc)
          by auto
      qed
    next
      case c
      have pd: "delta' x1 y1 x2 y2 \<noteq> 0"
        using c unfolding e'_aff_1_def by simp

      have ds: "delta x2 y2 x2 (-y2) \<noteq> 0 \<or>
                delta' x2 y2 (x2) (-y2) \<noteq> 0 "
        using in_aff d_n1 add_self by blast
      
      have eq1: "proj_addition ?g1 ?g2 = gluing `` {(ext_add (x1, y1) (x2, y2), 0)}" 
        (is "_ = ?g_add")
        using gluing_ext_add[OF assms(1,2) pd] by force
      then obtain rx ry where r_expr: 
        "rx = fst (ext_add (x1, y1) (x2, y2))"
        "ry = snd (ext_add (x1, y1) (x2, y2))"
        "(rx,ry) = ext_add (x1,y1) (x2,y2)"
        by simp
      have in_aff_r: "(rx,ry) \<in> e'_aff"
        using in_aff ext_add_closure_points pd r_expr by auto  
      have e_proj_r: "gluing `` {((rx,ry), 0)} \<in> e_proj"
        using e_proj_aff in_aff_r by auto
       
      consider
        (aa) "(rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry))" |
        (bb) "((rx, ry), i (x2, y2)) \<in> e'_aff_0" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry)))" |
        (cc) "((rx, ry), i (x2, y2)) \<in> e'_aff_1" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. i (x2, y2) = (g \<circ> i) (rx, ry)))" "((rx, ry), i (x2, y2)) \<notin> e'_aff_0"        
        using dichotomy_1[OF in_aff_r in_aff(3)] by fast        
      then show ?thesis 
      proof(cases)
        case aa
        then obtain g where g_expr: 
          "g \<in> symmetries" "(i (x2, y2)) = (g \<circ> i) (rx, ry)" by blast
        then obtain r where rot_expr: 
          "r \<in> rotations" "(i (x2, y2)) = (\<tau> \<circ> r \<circ> i) (rx, ry)" "\<tau> \<circ> g = r" 
          using sym_decomp pointfree_idE sym_to_rot tau_idemp by fastforce
       
        have e_proj_sym: "gluing `` {(g (i (rx, ry)), 0)} \<in> e_proj"
                         "gluing `` {(i (rx, ry), 0)} \<in> e_proj"
          using assms(3) g_expr(2) apply force
          using e_proj_r proj_add_class_inv(2) by blast
        
        from aa have pd': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) = 0"
          using wd_d_nz by auto
        consider
          (aaa) "(rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (i (x2, y2)) = (g \<circ> i) (rx, ry))" |
          (bbb) "((rx, ry), \<tau> (i (x2, y2))) \<in> e'_aff_0" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (i (x2, y2)) = (g \<circ> i) (rx, ry)))" |
          (ccc) "((rx, ry), \<tau> (i (x2, y2))) \<in> e'_aff_1" "\<not> ((rx, ry) \<in> e_circ \<and> (\<exists>g\<in>symmetries. \<tau> (i (x2, y2)) = (g \<circ> i) (rx, ry)))" "((rx, ry), \<tau> (i (x2, y2))) \<notin> e'_aff_0"        
          using dichotomy_1[OF in_aff_r taus] by fast
        then show ?thesis 
        proof(cases)
          case aaa 
          have pd'': "delta rx ry (fst (\<tau> (i (x2, y2)))) (snd (\<tau> (i (x2, y2)))) = 0"
            using wd_d_nz aaa by auto
          from aaa obtain g' where g'_expr: 
            "g' \<in> symmetries" "\<tau> (i (x2, y2)) = (g' \<circ> i) (rx, ry)" 
            by blast
          then obtain r' where r'_expr: 
            "r' \<in> rotations" "\<tau> (i (x2, y2)) = (\<tau> \<circ> r' \<circ> i) (rx, ry)" 
            using sym_decomp by blast
          from r'_expr have 
            "i (x2, y2) = (r' \<circ> i) (rx, ry)" 
            using tau_idemp_point by (metis comp_apply)
          from this rot_expr have "(\<tau> \<circ> r \<circ> i) (rx, ry) = (r' \<circ> i) (rx, ry)" 
            by argo
          then obtain ri' where "ri' \<in> rotations" "ri'( (\<tau> \<circ> r \<circ> i) (rx, ry)) = i (rx, ry)"
            by (metis comp_def rho_i_com_inverses(1) r'_expr(1) rot_inv tau_idemp tau_sq)
          then have "(\<tau> \<circ> ri' \<circ> r \<circ> i) (rx, ry) = i (rx, ry)"
            by (metis comp_apply rot_tau_com)
          then obtain g'' where g''_expr: "g'' \<in> symmetries" "g'' (i ((rx, ry))) = i (rx,ry)"
            using \<open>ri' \<in> rotations\<close> rot_expr(1) rot_comp tau_rot_sym by force
          then show ?thesis 
          proof -
            have in_g: "g'' \<in> G"
              using g''_expr(1) unfolding G_def symmetries_def by blast
            have in_circ: "i (rx, ry) \<in> e_circ"
              using aa i_circ by blast
            then have "g'' = id"
              using g_no_fp in_g in_circ g''_expr(2) by blast
            then have "False"
              using sym_not_id sym_decomp  g''_expr(1) by fastforce
            then show ?thesis by simp
          qed
        next
          case bbb  
          then have pd': "delta rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
            unfolding e'_aff_0_def by simp          
          then have pd'': "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
            using 1 delta'_add_delta_2 in_aff pd r_expr by meson
          have "False"
            using aa pd'' wd_d'_nz by auto
          then show ?thesis by auto
        next 
          case ccc 
          then have pd': "delta' rx ry (fst (\<tau> (i (x2,y2)))) (snd (\<tau> (i (x2,y2)))) \<noteq> 0"
            unfolding e'_aff_0_def e'_aff_1_def by auto
          then have pd'': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
            using 1 delta'_add_delta_1 in_aff pd r_expr by auto
          have "False"
            using aa pd'' wd_d_nz by auto      
          then show ?thesis by auto
        qed
      next
        case bb        
        then have pd': "delta rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
          using bb unfolding e'_aff_0_def r_expr by simp
        have add_assoc: "add (ext_add (x1, y1) (x2, y2)) (i (x2, y2)) = (x1,y1)"
        proof(cases "delta x2 y2 x2 (-y2) \<noteq> 0")
          case True
          have inv: "add (x2, y2) (i (x2, y2)) = (1,0)"
            using inverse_generalized[OF in_aff(2)] True
            unfolding delta_def delta_minus_def delta_plus_def by auto
          show ?thesis
            apply(subst add_ext_add_add_assoc_points[OF in_aff(1,2), 
                 of "fst (i (x2,y2))" "snd (i (x2,y2))",
                 simplified prod.collapse])  
            using in_aff(3) pd True pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        next
          case False
          then have ds': "delta' x2 y2 x2 (- y2) \<noteq> 0"
            using ds by auto
          have inv: "ext_add (x2, y2) (i (x2, y2)) = (1,0)"
            using ext_add_inverse 1 by simp
          show ?thesis
            apply(subst add_ext_add_ext_assoc_points[of x1 y1 x2 y2 
                  "fst (i (x2,y2))" "snd (i (x2,y2))", simplified prod.collapse]) 
            using in_aff pd ds' pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        qed

        show ?thesis 
          apply(subst gluing_ext_add,(simp add: e_proj pd del: ext_add.simps i.simps)+)
          apply(subst gluing_add[of rx ry 0 "fst (i (x2,y2))" "snd (i (x2,y2))",
                         simplified r_expr prod.collapse])         
          using e_proj_r r_expr e_proj pd' apply(simp,simp,simp)
          apply(subst add_assoc)
          by auto
      next
        case cc 
        then have pd': "delta' rx ry (fst (i (x2,y2))) (snd (i (x2,y2))) \<noteq> 0"
          using cc unfolding e'_aff_1_def r_expr by simp
        have add_assoc: "ext_add (ext_add (x1, y1) (x2, y2)) (i (x2, y2)) = (x1,y1)"
        proof(cases "delta x2 y2 x2 (-y2) \<noteq> 0")
          case True
          have inv: "add (x2, y2) (i (x2, y2)) = (1,0)"
            using inverse_generalized[OF in_aff(2)] True
            unfolding delta_def delta_minus_def delta_plus_def by auto
          show ?thesis
            apply(subst ext_ext_add_add_assoc_points[OF in_aff(1,2), 
                 of "fst (i (x2,y2))" "snd (i (x2,y2))",
                 simplified prod.collapse])  
            using in_aff(3) pd True pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        next
          case False
          then have ds': "delta' x2 y2 x2 (- y2) \<noteq> 0"
            using ds by auto
          have inv: "ext_add (x2, y2) (i (x2, y2)) = (1,0)"
            using ext_add_inverse 1 by simp
          show ?thesis
            apply(subst ext_ext_add_ext_assoc_points[of x1 y1 x2 y2 
                  "fst (i (x2,y2))" "snd (i (x2,y2))", simplified prod.collapse]) 
            using in_aff pd ds' pd' r_expr apply force+
            using inv unfolding delta_def delta_plus_def delta_minus_def apply simp
            using inv neutral by presburger
        qed

        show ?thesis
          apply(subst gluing_ext_add,(simp add: e_proj pd del: ext_add.simps i.simps)+)
          apply(subst gluing_ext_add[of rx ry 0 "fst (i (x2,y2))" "snd (i (x2,y2))",
                         simplified r_expr prod.collapse])         
          using e_proj_r r_expr e_proj pd' apply(simp,simp,simp)
          apply(subst add_assoc)
          by auto
      qed
    qed
  next
    case 2
    (*TODO: rewrite this proof *)
    then have "(\<exists> r \<in> rotations. (x1,y1) = r (1,0)) \<or> (\<exists> r \<in> rotations. (x2,y2) = r (1,0))"
      using in_aff(1,2) unfolding e'_aff_def e'_def 
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

        have "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}) =
              proj_addition (tf r (gluing `` {((1, 0), 0)})) (gluing `` {((x2, y2), 0)})" 
          using remove_rotations[OF one_in rot_expr(1)] rot_expr(2) by presburger
        also have "... = tf r (proj_addition (gluing `` {((1, 0), 0)}) (gluing `` {((x2, y2), 0)}))"  
          using remove_add_rotation assms rot_expr one_in by presburger
        also have "... = tf r (gluing `` {((x2, y2), 0)})"
          using proj_add_class_identity 
          by (simp add: e_proj(2) identity_equiv)
        finally have eq1: "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}) =
                           tf r (gluing `` {((x2, y2), 0)})" by argo

        have "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {(i (x2, y2), 0)}) =
              proj_addition (tf r (gluing `` {((x2, y2), 0)})) (gluing `` {(i (x2, y2), 0)})"
          using eq1 by argo
        also have "... = tf r (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {(i (x2, y2), 0)}))"
          using remove_add_rotation rot_expr well_defined proj_addition_def assms one_in by simp
        also have "... = tf r (gluing `` {((1, 0), 0)})"
          using proj_addition_def proj_add_class_inv assms 
          by (simp add: identity_equiv)
        finally have eq2: "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {(i (x2, y2), 0)}) =
                           tf r (gluing `` {((1, 0), 0)})" by blast
        show ?thesis 
          apply(subst eq2)
          using remove_rotations[OF one_in rot_expr(1)] rot_expr(2) by presburger
      next
        case b
        then obtain r where rot_expr: "r \<in> rotations" "(x2, y2) = r (1, 0)" by blast
        then obtain r' where rot_expr': "r' \<in> rotations" "i (x2, y2) = r' (i (1, 0))" "r \<circ> r' = id" 
          using rotations_i_inverse[OF rot_expr(1)]
          by (metis (no_types, hide_lams) comp_apply comp_assoc comp_id diff_0 diff_zero i.simps id_apply id_comp rot_inv)
        have "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}) =
              proj_addition (gluing `` {((x1, y1), 0)}) (tf r (gluing `` {((1, 0), 0)}))" 
          using remove_rotations[OF one_in rot_expr(1)] rot_expr(2) by presburger
        also have "... = tf r (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((1, 0), 0)}))"  
          using remove_add_rotation assms rot_expr one_in          
          by (metis proj_addition_comm remove_rotations)
        also have "... = tf r (gluing `` {((x1, y1), 0)})"
          using proj_add_class_identity assms 
                identity_equiv one_in proj_addition_comm by metis
        finally have eq1: "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}) =
                           tf r (gluing `` {((x1, y1), 0)})" by argo

        have "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {(i (x2, y2), 0)}) =
              proj_addition (tf r (gluing `` {((x1, y1), 0)})) (gluing `` {(i (x2, y2), 0)})"
          using eq1 by argo
        also have "... = tf r (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {(i (x2, y2), 0)}))"
          using remove_add_rotation rot_expr well_defined proj_addition_def assms one_in by simp
        also have "... = tf r (proj_addition (gluing `` {((x1, y1), 0)}) (tf r' (gluing `` {(i (1, 0), 0)})))"
          using remove_rotations one_in rot_expr' by simp
        also have "... = tf r (tf r' (proj_addition (gluing `` {((x1, y1), 0)}) ((gluing `` {(i (1, 0), 0)}))))"
          using proj_add_class_inv assms 
          by (metis i.simps one_in proj_addition_comm remove_add_rotation rot_expr'(1) rotation_preserv_e_proj)
        also have "... = tf (id) (proj_addition (gluing `` {((x1, y1), 0)}) ((gluing `` {((1, 0), 0)})))"
          using tf_comp rot_expr'  by force
        also have "... = (gluing `` {((x1, y1), 0)})"
          apply(subst tf_id)
          by (simp add: e_proj(1) identity_equiv identity_proj 
             proj_addition_comm proj_add_class_identity)        
        finally have eq2: "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {(i (x2, y2), 0)}) =
                           (gluing `` {((x1, y1), 0)})" by blast
        show ?thesis by(subst eq2,simp) 
      qed
    qed
  qed

lemma e'_aff_0_invariance:
  "((x,y),(x',y')) \<in> e'_aff_0 \<Longrightarrow> ((x',y'),(x,y)) \<in> e'_aff_0"
  unfolding e'_aff_0_def
  apply(subst (1) prod.collapse[symmetric])
  apply(simp)
  unfolding delta_def delta_plus_def delta_minus_def
  by algebra

lemma e'_aff_1_invariance:
  "((x,y),(x',y')) \<in> e'_aff_1 \<Longrightarrow> ((x',y'),(x,y)) \<in> e'_aff_1"
  unfolding e'_aff_1_def
  apply(subst (1) prod.collapse[symmetric])
  apply(simp)
  unfolding delta'_def delta_x_def delta_y_def
  by algebra

(* TODO: a tactic in ML to prove associativity *)

lemma assoc_1:
  assumes "gluing `` {((x1, y1), 0)}  \<in> e_proj" 
          "gluing `` {((x2, y2), 0)} \<in> e_proj" 
          "gluing `` {((x3, y3), 0)} \<in> e_proj"
  assumes a: "g \<in> symmetries" "(x2, y2) = (g \<circ> i) (x1, y1)"
  shows 
    "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}) = 
     tf'' (\<tau> \<circ> g) {((1,0),0)}" (is "proj_addition ?g1 ?g2 = _")
    "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {((x3, y3), 0)}) =
     tf'' (\<tau> \<circ> g) (gluing `` {((x3, y3), 0)})" 
    "proj_addition (gluing `` {((x1, y1), 0)}) (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)})) =
     tf'' (\<tau> \<circ> g) (gluing `` {((x3, y3), 0)})" (is "proj_addition ?g1 (proj_addition ?g2 ?g3) = _")
proof -
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have one_in: "{((1, 0), 0)} \<in> e_proj" 
    using identity_proj by force

  have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

  have e_proj: "gluing `` {(g (i (x1, y1)), 0)}  \<in> e_proj"
               "gluing `` {(i (x1, y1), 0)}  \<in> e_proj" (is "?ig1 \<in> _") 
               "proj_addition (gluing `` {(i (x1, y1), 0)}) (gluing `` {((x3, y3), 0)}) \<in> e_proj"
    using assms(2,5) apply auto[1]
    using assms(1) proj_add_class_inv(2) apply auto[1]
    using assms(1,3) proj_add_class_inv(2) well_defined by blast

  show 1: "proj_addition ?g1 ?g2 = tf'' (\<tau> \<circ> g) {((1,0),0)}" 
  proof -
    have eq1: "?g2 = tf'' (\<tau> \<circ> g) ?ig1"
      apply(simp add: assms(5))
      apply(subst (2 5) prod.collapse[symmetric])
      apply(subst remove_sym)
      using e_proj assms by auto
    have eq2: "proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1) = 
               tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
      apply(subst (1 2) proj_addition_comm)
      using assms e_proj apply(simp,simp)
      using assms(2) eq1 apply auto[1]
      apply(subst remove_add_sym)
      using assms(1) e_proj(2) rot by auto  
   have eq3: "tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1) = tf'' (\<tau> \<circ> g) {((1,0),0)}"
     using assms(1) proj_add_class_inv by auto
   show ?thesis using eq1 eq2 eq3 by presburger
  qed

  have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
        proj_addition (tf'' (\<tau> \<circ> g) {((1,0),0)}) ?g3"
    using 1 by force
  also have "... = tf'' (\<tau> \<circ> g) (proj_addition ({((1,0),0)}) ?g3)"
    by (simp add: assms(3) one_in remove_add_sym rot)
  also have "... = tf'' (\<tau> \<circ> g) ?g3"
    using assms(3) identity_equiv proj_add_class_identity by simp
  finally show 2: "proj_addition (proj_addition ?g1 ?g2) ?g3 = tf'' (\<tau> \<circ> g) ?g3"
    by blast

  have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
    proj_addition ?g1 (proj_addition (gluing `` {(g (i (x1, y1)), 0)}) ?g3)"
      using assms by simp
  also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) (proj_addition (gluing `` {(i (x1, y1), 0)}) ?g3))"
  proof -
    have eq1: "gluing `` {(g (i (x1, y1)), 0)} = tf'' (\<tau> \<circ> g) ?ig1"
      apply(subst (2 5) prod.collapse[symmetric])
      apply(subst remove_sym)
      using e_proj assms by auto
    have eq2: "proj_addition (tf'' (\<tau> \<circ> g) ?ig1) ?g3 = 
               tf'' (\<tau> \<circ> g) (proj_addition ?ig1 ?g3)"
      apply(subst remove_add_sym)
      using assms(3) e_proj(2) rot by auto

    show ?thesis using eq1 eq2 by presburger
  qed 
  also have "... = tf'' (\<tau> \<circ> g)  (proj_addition ?g1 (proj_addition ?ig1 ?g3))"
    apply(subst (1 3) proj_addition_comm)
    using assms apply simp
    using e_proj(3) apply auto[1]
     apply (metis assms(3) e_proj(2) i.simps remove_add_sym rot 
                 tf''_preserv_e_proj well_defined)
    apply(subst remove_add_sym)  
    using e_proj(3) assms(1) rot by auto
  also have "... = tf'' (\<tau> \<circ> g) ?g3"
  proof -
    have "proj_addition ?g1 (proj_addition ?ig1 ?g3) = ?g3"
      apply(subst (1 2) proj_addition_comm)
      using e_proj assms apply (simp,simp,simp)
      using assms(3) e_proj(2) well_defined apply auto[1]
      using cancellation_assoc i_idemp_explicit 
      by (metis assms(1) assms(3) e_proj(2) i.simps)
    then show ?thesis by argo
  qed
  finally show 3: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                   tf'' (\<tau> \<circ> g) ?g3" by blast
qed 

lemma assoc_11:
  assumes "gluing `` {((x1, y1), 0)}  \<in> e_proj" "gluing `` {((x2, y2), 0)} \<in> e_proj" "gluing `` {((x3, y3), 0)} \<in> e_proj"
  assumes a: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) (x2, y2)"
  shows 
    "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {((x3, y3), 0)}) = 
     proj_addition (gluing `` {((x1, y1), 0)}) (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)}))"
    (is "proj_addition (proj_addition ?g1 ?g2) ?g3 = _")
proof -
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have one_in: "{((1, 0), 0)} \<in> e_proj" 
    using identity_equiv identity_proj by auto

  have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

  have e_proj: "gluing `` {(g (i (x2, y2)), 0)}  \<in> e_proj"
               "gluing `` {(i (x2, y2), 0)}  \<in> e_proj" (is "?ig2 \<in> _") 
               "proj_addition ?g1 ?g2 \<in> e_proj"
    using assms(3,5) apply simp
    using proj_add_class_inv assms(2) apply fast
    using assms(1,2) well_defined by simp

  have eq1: "?g3 = tf'' (\<tau> \<circ> g) ?ig2"
    apply(subst a)
    apply(subst comp_apply)
    apply(subst (2) prod.collapse[symmetric])
    apply(subst remove_sym[OF _ _ assms(4)])
    using e_proj apply(simp,simp) 
    by(subst prod.collapse,simp) 
  have eq2: "proj_addition (proj_addition ?g1 ?g2) (tf'' (\<tau> \<circ> g) ?ig2) = 
             tf'' (\<tau> \<circ> g) ?g1"
    apply(subst (2) proj_addition_comm)
    using e_proj eq1 assms(3) apply(simp,simp)
    apply(subst remove_add_sym)
    using e_proj rot apply(simp,simp,simp)
    apply(subst proj_addition_comm)
    using e_proj apply(simp,simp)
    apply(subst cancellation_assoc)
    using assms(1,2) e_proj by(simp,simp,simp,simp)
  have eq3: "proj_addition ?g2 (tf'' (\<tau> \<circ> g) ?ig2) = 
             tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
    apply(subst proj_addition_comm)
    using e_proj eq1 assms(2,3) apply(simp,simp)
    apply(subst remove_add_sym)
    using e_proj rot assms(2) apply(simp,simp,simp)
    apply(subst proj_addition_comm)
    using e_proj eq1 assms(2,3) apply(simp,simp)
    apply(subst proj_add_class_inv(1)) 
    using assms(2) apply blast
    by simp

  show ?thesis
    apply(subst eq1)
    apply(subst eq2)
    apply(subst eq1)
    apply(subst eq3)
    apply(subst proj_addition_comm)
    using assms(1) apply(simp)
    using tf''_preserv_e_proj[OF _ rot] one_in identity_equiv apply metis
    apply(subst remove_add_sym)
    using identity_equiv one_in assms(1) rot apply(argo,simp,simp)
    apply(subst proj_add_class_identity)
    using assms(1) apply(simp)
    by blast
qed 

lemma assoc_111_add:
  assumes "gluing `` {((x1, y1), 0)}  \<in> e_proj" "gluing `` {((x2, y2), 0)} \<in> e_proj" "gluing `` {((x3, y3), 0)} \<in> e_proj"
  assumes 22: "g\<in>symmetries" "(x1, y1) = (g \<circ> i) (add (x2,y2) (x3,y3))" "((x2, y2), x3, y3) \<in> e'_aff_0"
  shows 
    "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {((x3, y3), 0)}) = 
     proj_addition (gluing `` {((x1, y1), 0)}) (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)}))"
    (is "proj_addition (proj_addition ?g1 ?g2) ?g3 = _") 
proof -
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have e_proj_0: "gluing `` {(i (x1,y1), 0)} \<in> e_proj" (is "?ig1 \<in> _")
                 "gluing `` {(i (x2,y2), 0)} \<in> e_proj" (is "?ig2 \<in> _")
                 "gluing `` {(i (x3,y3), 0)} \<in> e_proj" (is "?ig3 \<in> _")
    using assms proj_add_class_inv by blast+
  
  have p_delta: "delta x2 y2 x3 y3 \<noteq> 0"
                "delta (fst (i (x2,y2))) (snd (i (x2,y2))) 
                       (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 22 unfolding e'_aff_0_def apply simp
        using 22 unfolding e'_aff_0_def delta_def delta_plus_def delta_minus_def by simp

  define add_2_3 where "add_2_3 = add (x2,y2) (x3,y3)"
  have add_in: "add_2_3 \<in> e'_aff"
    unfolding e'_aff_def add_2_3_def
    apply(simp del: add.simps)
    apply(subst (2) prod.collapse[symmetric])
    apply(standard)
    apply(simp del: add.simps add: e_e'_iff[symmetric])        
    apply(subst add_closure)
    using in_aff e_e'_iff 22 unfolding e'_aff_def e'_aff_0_def delta_def by(fastforce)+
  have e_proj_2_3: "gluing `` {(add_2_3, 0)} \<in> e_proj" 
                   "gluing `` {(i add_2_3, 0)} \<in> e_proj" 
    using add_in add_2_3_def e_proj_aff apply simp
    using add_in add_2_3_def e_proj_aff proj_add_class_inv by auto
          
  from 22 have g_expr: "g \<in> symmetries" "(x1,y1) = (g \<circ> i) add_2_3" unfolding add_2_3_def by auto
  then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot by blast

  have e_proj_2_3_g: "gluing `` {(g (i add_2_3), 0)} \<in> e_proj" 
    using e_proj_2_3 g_expr assms(1) by auto

  have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
        proj_addition (gluing `` {((g \<circ> i) add_2_3, 0)}) (proj_addition ?g2 ?g3)" 
    using g_expr by simp
  also have "... = proj_addition (gluing `` {((g \<circ> i) add_2_3, 0)}) (gluing `` {(add_2_3, 0)}) " 
    using gluing_add add_2_3_def p_delta assms(2,3) by force
  also have "... = tf'' (\<tau> \<circ> g) (proj_addition (gluing `` {(i add_2_3, 0)}) (gluing `` {(add_2_3, 0)}))"
    apply(subst comp_apply,subst (2) prod.collapse[symmetric])          
    apply(subst remove_sym)
    using g_expr e_proj_2_3 e_proj_2_3_g apply(simp,simp,simp)
    apply(subst remove_add_sym)
    using e_proj_2_3 e_proj_2_3_g rot by auto
  also have "... = tf'' (\<tau> \<circ> g) {((1,0), 0)}"    
    apply(subst proj_addition_comm)
    using add_2_3_def e_proj_2_3(1) proj_add_class_inv by auto
  finally have eq1: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                     tf'' (\<tau> \<circ> g) {((1,0), 0)}"
    by auto

  have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
  proj_addition (proj_addition (gluing `` {((g \<circ> i) add_2_3, 0)}) ?g2) ?g3"
    using g_expr by argo
  also have "... = proj_addition (tf'' (\<tau> \<circ> g)
      (proj_addition (gluing `` {(i add_2_3, 0)}) ?g2)) ?g3"
    apply(subst comp_apply,subst (2) prod.collapse[symmetric])          
    apply(subst remove_sym)
    using g_expr e_proj_2_3 e_proj_2_3_g apply(simp,simp,simp)
    apply(subst remove_add_sym)
    using e_proj_2_3 e_proj_2_3_g assms(2) rot by auto
  also have "... =  proj_addition (tf'' (\<tau> \<circ> g)
      (proj_addition (proj_addition ?ig2 ?ig3) ?g2)) ?g3"        
    unfolding add_2_3_def
    apply(subst inverse_rule_3)
    using gluing_add e_proj_0 p_delta by force
  also have "... = proj_addition (tf'' (\<tau> \<circ> g) ?ig3) ?g3"    
    using cancellation_assoc 
  proof -
    have "proj_addition ?g2 (proj_addition ?ig3 ?ig2) = ?ig3"
      by (metis (no_types, lifting) assms(2) cancellation_assoc e_proj_0(2) e_proj_0(3) i.simps i_idemp_explicit proj_addition_comm well_defined)
    then show ?thesis
      using assms(2) e_proj_0(2) e_proj_0(3) proj_addition_comm well_defined by auto
  qed
  also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?ig3 ?g3)"
    apply(subst remove_add_sym)
    using assms(3) rot e_proj_0(3) by auto
  also have "... = tf'' (\<tau> \<circ> g) {((1,0), 0)}"
    apply(subst proj_addition_comm)
    using assms(3) proj_add_class_inv by auto
  finally have eq2: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                     tf'' (\<tau> \<circ> g) {((1,0), 0)}" by blast
  show ?thesis using eq1 eq2 by argo
qed 

lemma assoc_111_ext_add:
  assumes "gluing `` {((x1, y1), 0)}  \<in> e_proj" "gluing `` {((x2, y2), 0)} \<in> e_proj" "gluing `` {((x3, y3), 0)} \<in> e_proj"
  assumes 22: "g\<in>symmetries" "(x1, y1) = (g \<circ> i) (ext_add (x2,y2) (x3,y3))" "((x2, y2), x3, y3) \<in> e'_aff_1"
  shows 
    "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {((x3, y3), 0)}) = 
     proj_addition (gluing `` {((x1, y1), 0)}) (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)}))" 
  (is "proj_addition (proj_addition ?g1 ?g2) ?g3 = _") 
proof -
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have one_in: "gluing `` {((1, 0), 0)} \<in> e_proj"
    using identity_equiv identity_proj by force

  have e_proj_0: "gluing `` {(i (x1,y1), 0)} \<in> e_proj" (is "?ig1 \<in> e_proj")
                 "gluing `` {(i (x2,y2), 0)} \<in> e_proj" (is "?ig2 \<in> e_proj")
                 "gluing `` {(i (x3,y3), 0)} \<in> e_proj" (is "?ig3 \<in> e_proj")
    using assms proj_add_class_inv by blast+
  
  have p_delta: "delta' x2 y2 x3 y3 \<noteq> 0"
                "delta' (fst (i (x2,y2))) (snd (i (x2,y2))) 
                        (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 22 unfolding e'_aff_1_def apply simp
        using 22 unfolding e'_aff_1_def delta'_def delta_x_def delta_y_def by force

  define add_2_3 where "add_2_3 = ext_add (x2,y2) (x3,y3)"
  have add_in: "add_2_3 \<in> e'_aff"
    unfolding e'_aff_def add_2_3_def
    apply(simp del: ext_add.simps)
    apply(subst (2) prod.collapse[symmetric])
    apply(standard)
    apply(subst ext_add_closure)
    using in_aff 22 unfolding e'_aff_def e'_aff_1_def by(fastforce)+

  have e_proj_2_3: "gluing `` {(add_2_3, 0)} \<in> e_proj" 
                   "gluing `` {(i add_2_3, 0)} \<in> e_proj" 
    using add_in add_2_3_def e_proj_aff apply simp
    using add_in add_2_3_def e_proj_aff proj_add_class_inv by auto
     
     
  from 22 have g_expr: "g \<in> symmetries" "(x1,y1) = (g \<circ> i) add_2_3" unfolding add_2_3_def by auto
  then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot by blast

  have e_proj_2_3_g: "gluing `` {(g (i add_2_3), 0)} \<in> e_proj" 
    using e_proj_2_3 g_expr assms(1) by auto

  have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
        proj_addition (gluing `` {((g \<circ> i) add_2_3, 0)}) (proj_addition ?g2 ?g3)" 
    using g_expr by simp
  also have "... = proj_addition (gluing `` {((g \<circ> i) add_2_3, 0)}) (gluing `` {(add_2_3, 0)}) " 
    using gluing_ext_add add_2_3_def p_delta assms(2,3) by force
  also have "... = tf'' (\<tau> \<circ> g) (proj_addition (gluing `` {(i add_2_3, 0)}) (gluing `` {(add_2_3, 0)}))"
    apply(subst comp_apply,subst (2) prod.collapse[symmetric])          
    apply(subst remove_sym)
    using g_expr e_proj_2_3 e_proj_2_3_g apply(simp,simp,simp)
    apply(subst remove_add_sym)
    using e_proj_2_3 e_proj_2_3_g rot by auto
  also have "... = tf'' (\<tau> \<circ> g) {((1,0), 0)}"     
    apply(subst proj_addition_comm)
    using add_2_3_def e_proj_2_3(1) proj_add_class_inv by auto
  finally have eq1: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                     tf'' (\<tau> \<circ> g) {((1,0), 0)}"
    by auto

  have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
        proj_addition (proj_addition (gluing `` {((g \<circ> i) add_2_3, 0)}) ?g2) ?g3"
    using g_expr by argo
  also have "... = proj_addition (tf'' (\<tau> \<circ> g)
                   (proj_addition (gluing `` {(i add_2_3, 0)}) ?g2)) ?g3"
    apply(subst comp_apply,subst (2) prod.collapse[symmetric])          
    apply(subst remove_sym)
    using g_expr e_proj_2_3 e_proj_2_3_g apply(simp,simp,simp)
    apply(subst remove_add_sym)
    using e_proj_2_3 e_proj_2_3_g assms(2) rot by auto
  also have "... =  proj_addition (tf'' (\<tau> \<circ> g)
      (proj_addition (proj_addition ?ig2 ?ig3) ?g2)) ?g3"        
    unfolding add_2_3_def
    apply(subst inverse_rule_4)
    using gluing_ext_add e_proj_0 p_delta by force
  also have "... = proj_addition (tf'' (\<tau> \<circ> g) ?ig3) ?g3"    
  proof -
    have "proj_addition ?g2 (proj_addition ?ig3 ?ig2) = ?ig3"
      apply(subst proj_addition_comm)
      using assms e_proj_0 well_defined apply(simp,simp)
      apply(subst cancellation_assoc[of "fst (i (x3,y3))" "snd (i (x3,y3))"
                                "fst (i (x2,y2))" "snd (i (x2,y2))",  
                             simplified prod.collapse i_idemp_explicit])
      using assms e_proj_0 by auto
    then show ?thesis
      using assms(2) e_proj_0(2) e_proj_0(3) proj_addition_comm well_defined by auto
  qed
  also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?ig3 ?g3)"
    apply(subst remove_add_sym)
    using assms(3) rot e_proj_0(3) by auto
  also have "... = tf'' (\<tau> \<circ> g) {((1,0), 0)}"
    using assms(3) proj_add_class_inv proj_addition_comm by auto
  finally have eq2: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                     tf'' (\<tau> \<circ> g) {((1,0), 0)}" by blast

  show ?thesis using eq1 eq2 by argo
qed 

lemma assoc_with_zeros:
  assumes "gluing `` {((x1, y1), 0)}  \<in> e_proj" 
          "gluing `` {((x2, y2), 0)} \<in> e_proj" 
          "gluing `` {((x3, y3), 0)} \<in> e_proj"
  shows "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)})) (gluing `` {((x3, y3), 0)}) = 
         proj_addition (gluing `` {((x1, y1), 0)}) (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)}))"
  (is "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
       proj_addition ?g1 (proj_addition ?g2 ?g3)")
proof -
  have in_aff: "(x1,y1) \<in> e'_aff" "(x2,y2) \<in> e'_aff" "(x3,y3) \<in> e'_aff" 
    using assms(1,2,3) e_proj_aff by auto

  have e_proj_0: "gluing `` {(i (x1,y1), 0)} \<in> e_proj" (is "?ig1 \<in> e_proj")
                 "gluing `` {(i (x2,y2), 0)} \<in> e_proj" (is "?ig2 \<in> e_proj")
                 "gluing `` {(i (x3,y3), 0)} \<in> e_proj" (is "?ig3 \<in> e_proj")    
    using assms proj_add_class_inv by auto
 
  consider
    (1) "(\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1))" |
    (2) "((x1, y1), x2, y2) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1)))" |
    (3) "((x1, y1), x2, y2) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x2, y2) = (g \<circ> i) (x1, y1)))" "((x1, y1), x2, y2) \<notin> e'_aff_0"
    using dichotomy_1 in_aff by blast
  then show ?thesis
  proof(cases)
    case 1 then show ?thesis using assoc_1(2,3) assms by force
  next
    case 2
    have p_delta_1_2: "delta x1 y1 x2 y2 \<noteq> 0"
                      "delta (fst (i (x1, y1))) (snd (i (x1, y1))) 
                             (fst (i (x2, y2))) (snd (i (x2, y2))) \<noteq> 0" 
        using 2 unfolding e'_aff_0_def apply simp
        using 2 in_aff unfolding e'_aff_0_def delta_def delta_minus_def delta_plus_def   
        by auto

    define add_1_2 where "add_1_2 = add (x1, y1) (x2, y2)"
    have add_in_1_2: "add_1_2 \<in> e'_aff"
      unfolding e'_aff_def add_1_2_def
      apply(simp del: add.simps)
      apply(subst (2) prod.collapse[symmetric])
      apply(standard)
      apply(simp add: e_e'_iff[symmetric] del: add.simps)
      apply(subst add_closure)
      using in_aff p_delta_1_2(1) e_e'_iff 
      unfolding delta_def e'_aff_def by(blast,(simp)+) 

    have e_proj_1_2: "gluing `` {(add_1_2, 0)} \<in> e_proj" 
                     "gluing `` {(i add_1_2, 0)} \<in> e_proj" 
      using add_in_1_2 add_1_2_def e_proj_aff proj_add_class_inv by auto

    consider
      (11) "(\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2))" |
      (22) "((x2, y2), (x3, y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2)))" |
      (33) "((x2, y2), (x3, y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2)))" "((x2, y2), (x3, y3)) \<notin> e'_aff_0"
      using dichotomy_1 in_aff by blast
    then show ?thesis 
    proof(cases)
      case 11
      then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) (x2, y2)" by blast
      then show ?thesis  using assoc_11 assms by force
    next
      case 22
      have p_delta_2_3: "delta x2 y2 x3 y3 \<noteq> 0"
                    "delta (fst (i (x2,y2))) (snd (i (x2,y2))) 
                           (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 22 unfolding e'_aff_0_def apply simp
        using 22 unfolding e'_aff_0_def delta_def delta_plus_def delta_minus_def by simp

      define add_2_3 where "add_2_3 = add (x2,y2) (x3,y3)"
      have add_in: "add_2_3 \<in> e'_aff"
        unfolding e'_aff_def add_2_3_def
        apply(simp del: add.simps)
        apply(subst (2) prod.collapse[symmetric])
        apply(standard)
        apply(simp del: add.simps add: e_e'_iff[symmetric])        
        apply(subst add_closure)
        using in_aff e_e'_iff 22 unfolding e'_aff_def e'_aff_0_def delta_def by(fastforce)+
      have e_proj_2_3: "gluing `` {(add_2_3, 0)} \<in> e_proj" 
                       "gluing `` {(i add_2_3, 0)} \<in> e_proj" 
        using add_in add_2_3_def e_proj_aff apply simp
        using add_in add_2_3_def e_proj_aff proj_add_class_inv by auto

      consider
        (111) "(\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3)" |
        (222) "(add_2_3, (x1,y1)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" |
        (333) "(add_2_3, (x1,y1)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" "(add_2_3, (x1,y1)) \<notin> e'_aff_0"
        using add_in in_aff dichotomy_1 by blast        
      then show ?thesis   
      proof(cases)
        case 111                
        then show ?thesis using assoc_111_add using "22"(1) add_2_3_def assms(1) assms(2) assms(3) by blast
      next
        case 222
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_0" 
            apply(subst (3) prod.collapse[symmetric])
          using 222 e'_aff_0_invariance by fastforce 

        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) ({((1, 0), 0)})"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            by (metis cancellation_assoc e_proj_1_2(1) e_proj_1_2(2) identity_equiv 
                identity_proj prod.collapse proj_add_class_identity proj_addition_comm)
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) ({((1, 0), 0)})" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)})
                             ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_3,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2)
                              ?g2))"
          proof -
            have "gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_add[symmetric,of "fst (i (x1,y1))" "snd (i (x1,y1))" 0
                                            "fst (i (x2,y2))" "snd (i (x2,y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2) 
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) ({((1, 0), 0)})"
            using assms(1) proj_add_class_comm proj_add_class_inv by simp
          finally have eq2: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                             tf'' (\<tau> \<circ> g) ({((1, 0), 0)})" by auto
          then show ?thesis 
            using eq1 eq2 by blast
        next
          case 2222
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_add_add_add_assoc)
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_add_add_add_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1
                              (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed  
      next
        case 333 
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_1" 
          using 333(1) e'_aff_1_invariance  add_2_3_def by auto

        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            by (metis (no_types, lifting) cancellation_assoc e_proj_1_2(1) e_proj_1_2(2) identity_equiv 
                identity_proj prod.collapse proj_add_class_identity proj_addition_comm)
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)})
                              ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) 
            apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_3,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2) ?g2))"
          proof -
            have "gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_add[symmetric, of "fst (i (x1,y1))" "snd (i (x1,y1))" 0
                                             "fst (i (x2, y2))" "snd (i (x2, y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2)
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            using assms(1) proj_add_class_comm proj_addition_def proj_add_class_inv by simp
          finally have eq2: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by auto
          then show ?thesis using eq1 eq2 by blast
        next
          case 2222
          
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_add_ext_add_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by force+
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_1_def by(blast,auto)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_add_ext_add_assoc)
            apply(simp,simp) 
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by(force)+
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_1_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed
      qed
    next
      case 33
      have p_delta_2_3: "delta' x2 y2 x3 y3 \<noteq> 0"
                        "delta' (fst (i (x2,y2))) (snd (i (x2,y2))) 
                                (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 33 unfolding e'_aff_1_def apply simp
        using 33 unfolding e'_aff_1_def delta'_def delta_x_def delta_y_def by force

      define add_2_3 where "add_2_3 = ext_add (x2,y2) (x3,y3)"
      have add_in: "add_2_3 \<in> e'_aff"
        unfolding e'_aff_def add_2_3_def
        apply(simp del: ext_add.simps)
        apply(subst (2) prod.collapse[symmetric])
        apply(standard)
        apply(subst ext_add_closure)
        using in_aff e_e'_iff 33 unfolding e'_aff_def e'_aff_1_def delta'_def by(fastforce)+
      have e_proj_2_3: "gluing `` {(add_2_3, 0)} \<in> e_proj" 
                       "gluing `` {(i add_2_3, 0)} \<in> e_proj" 
        using add_in add_2_3_def e_proj_aff proj_add_class_inv by auto

      consider
        (111) "(\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3)" |
        (222) "(add_2_3, (x1,y1)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" |
        (333) "(add_2_3, (x1,y1)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" "(add_2_3, (x1,y1)) \<notin> e'_aff_0"
        using add_in in_aff dichotomy_1 by blast        
      then show ?thesis   
      proof(cases)
        case 111                
        then show ?thesis using assoc_111_ext_add using "33"(1) add_2_3_def assms(1) assms(2) assms(3) by blast
      next
        case 222
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_0" 
          apply(subst (3) prod.collapse[symmetric])
          using 222 e'_aff_0_invariance by fastforce 
        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            apply(subst proj_addition_comm)
            using e_proj_1_2 apply(simp,simp)
            apply(subst proj_add_class_inv(1)) 
            using e_proj_1_2 apply simp
            using e_proj_1_2(1) by auto
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)})
                              ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_3,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2) ?g2))"
          proof -
            have "gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_add[symmetric, of "fst (i (x1,y1))" "snd (i (x1,y1))" 0
                                             "fst (i (x2,y2))" "snd (i (x2,y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2)
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            using assms(1) proj_add_class_comm proj_addition_def proj_add_class_inv by auto
          finally have eq2: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast
          then show ?thesis using eq1 eq2 by blast
        next
          case 2222

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_add_add_ext_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by auto
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_add_add_ext_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed  
      next
        case 333
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_1" 
          using 333(1) e'_aff_1_invariance  add_2_3_def by auto

        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            apply(subst proj_addition_comm)
            using e_proj_1_2 rot apply(simp,simp)
            apply(subst proj_add_class_inv(1))
            using e_proj_1_2(1) by auto
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)})
                              ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_3,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2) ?g2))"
          proof -
            have "gluing `` {(add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_add[symmetric, of "fst (i (x1, y1))" "snd (i (x1, y1))" 0 
                                             "fst (i (x2, y2))" "snd (i (x2, y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2)
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            using assms(1) proj_add_class_comm proj_addition_def proj_add_class_inv by auto
          finally have eq2: "proj_addition (gluing `` {((x1, y1), 0)})
                              (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)})) = 
                        tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast
          then show ?thesis using eq1 eq2 by blast
        next
          case 2222
          
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_add_ext_ext_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by force+
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps            
            unfolding e'_aff_1_def by(blast,auto)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_add_ext_ext_assoc)
            apply(simp,simp) 
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by(force)+
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_1_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed
      qed 
    qed
  next
    case 3
    have p_delta_1_2: "delta' x1 y1 x2 y2 \<noteq> 0"
                      "delta' (fst (i (x1, y1))) (snd (i (x1, y1))) 
                             (fst (i (x2, y2))) (snd (i (x2, y2))) \<noteq> 0" 
      using 3 unfolding e'_aff_1_def apply simp
      using 3 in_aff unfolding e'_aff_1_def delta'_def delta_x_def delta_y_def   
      by auto

    define add_1_2 where "add_1_2 = ext_add (x1, y1) (x2, y2)"
    have add_in_1_2: "add_1_2 \<in> e'_aff"
      unfolding e'_aff_def add_1_2_def
      apply(simp del: ext_add.simps)
      apply(subst (2) prod.collapse[symmetric])
      apply(standard)
      apply(subst ext_add_closure)
      using in_aff p_delta_1_2(1) e_e'_iff 
      unfolding delta'_def e'_aff_def by(blast,(simp)+) 

    have e_proj_1_2: "gluing `` {(add_1_2, 0)} \<in> e_proj" 
                     "gluing `` {(i add_1_2, 0)} \<in> e_proj" 
      using add_in_1_2 add_1_2_def e_proj_aff proj_add_class_inv by auto

    consider
      (11) "(\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2))" |
      (22) "((x2, y2), (x3, y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2)))" |
      (33) "((x2, y2), (x3, y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3, y3) = (g \<circ> i) (x2, y2)))" "((x2, y2), (x3, y3)) \<notin> e'_aff_0"
      using dichotomy_1 in_aff by blast
    then show ?thesis 
    proof(cases)
      case 11
      then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) (x2, y2)" by blast
      then show ?thesis  using assoc_11 assms by force
    next
      case 22
      have p_delta_2_3: "delta x2 y2 x3 y3 \<noteq> 0"
                    "delta (fst (i (x2,y2))) (snd (i (x2,y2))) 
                           (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 22 unfolding e'_aff_0_def apply simp
        using 22 unfolding e'_aff_0_def delta_def delta_plus_def delta_minus_def by simp

      define add_2_3 where "add_2_3 = add (x2,y2) (x3,y3)"
      have add_in: "add_2_3 \<in> e'_aff"
        unfolding e'_aff_def add_2_3_def
        apply(simp del: add.simps)
        apply(subst (2) prod.collapse[symmetric])
        apply(standard)
        apply(simp del: add.simps add: e_e'_iff[symmetric])        
        apply(subst add_closure)
        using in_aff e_e'_iff 22 unfolding e'_aff_def e'_aff_0_def delta_def by(fastforce)+
      have e_proj_2_3: "gluing `` {(add_2_3, 0)} \<in> e_proj" 
                       "gluing `` {(i add_2_3, 0)} \<in> e_proj" 
        using add_in add_2_3_def e_proj_aff apply simp
        using add_in add_2_3_def e_proj_aff proj_add_class_inv by auto

      consider
        (111) "(\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3)" |
        (222) "(add_2_3, (x1,y1)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" |
        (333) "(add_2_3, (x1,y1)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" "(add_2_3, (x1,y1)) \<notin> e'_aff_0"
        using add_in in_aff dichotomy_1 by blast        
      then show ?thesis   
      proof(cases)
        case 111                
        then show ?thesis using assoc_111_add using "22"(1) add_2_3_def assms(1) assms(2) assms(3) by blast
      next
        case 222
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_0" 
            apply(subst (3) prod.collapse[symmetric])
          using 222 e'_aff_0_invariance by fastforce 

        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_ext_add assms(1,2) add_1_2_def by auto
          also have "... = tf'' (\<tau> \<circ> g) ({((1, 0), 0)})"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            by (metis cancellation_assoc e_proj_1_2(1) e_proj_1_2(2) identity_equiv identity_proj 
                prod.collapse proj_add_class_identity proj_addition_comm)
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) ({((1, 0), 0)})" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)})
                             ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_4,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2)
                              ?g2))"
          proof -
            have "gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_ext_add[symmetric,of "fst (i (x1,y1))" "snd (i (x1,y1))" 0
                                            "fst (i (x2,y2))" "snd (i (x2,y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2) 
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) ({((1, 0), 0)})"
            using assms(1) proj_add_class_comm proj_add_class_inv by simp
          finally have eq2: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                             tf'' (\<tau> \<circ> g) ({((1, 0), 0)})" by auto
          then show ?thesis 
            using eq1 eq2 by blast
        next
          case 2222
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_ext_add_add_assoc_points)
            using p_delta_1_2 p_delta_2_3 2222  assumps in_aff 
            unfolding add_1_2_def add_2_3_def e'_aff_0_def 
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_ext_add_add_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed  
      next
        case 333 
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_1" 
          using 333(1) e'_aff_1_invariance  add_2_3_def by auto

        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_ext_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            by (metis (no_types, lifting) cancellation_assoc e_proj_1_2(1) e_proj_1_2(2) identity_equiv 
                identity_proj prod.collapse proj_add_class_identity proj_addition_comm)
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)})
                              ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) 
            apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_4,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2) ?g2))"
          proof -
            have "gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_ext_add[symmetric, of "fst (i (x1,y1))" "snd (i (x1,y1))" 0
                                             "fst (i (x2, y2))" "snd (i (x2, y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2)
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            using assms(1) proj_add_class_comm proj_addition_def proj_add_class_inv by simp
          finally have eq2: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by auto
          then show ?thesis using eq1 eq2 by blast
        next
          case 2222
          
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_ext_ext_add_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by force+
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_1_def by(blast,auto)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_ext_ext_add_assoc)
            apply(simp,simp) 
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by(force)+
          also have "... = proj_addition ?g1 (gluing `` {(add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_1_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed
      qed
    next
      case 33
      have p_delta_2_3: "delta' x2 y2 x3 y3 \<noteq> 0"
                        "delta' (fst (i (x2,y2))) (snd (i (x2,y2))) 
                                (fst (i (x3,y3))) (snd (i (x3,y3))) \<noteq> 0" 
        using 33 unfolding e'_aff_1_def apply simp
        using 33 unfolding e'_aff_1_def delta'_def delta_x_def delta_y_def by fastforce

      define add_2_3 where "add_2_3 = ext_add (x2,y2) (x3,y3)"
      have add_in: "add_2_3 \<in> e'_aff"
        unfolding e'_aff_def add_2_3_def
        apply(simp del: ext_add.simps)
        apply(subst (2) prod.collapse[symmetric])
        apply(standard)
        apply(subst ext_add_closure)
        using in_aff e_e'_iff 33 unfolding e'_aff_def e'_aff_1_def delta'_def by(fastforce)+
      have e_proj_2_3: "gluing `` {(add_2_3, 0)} \<in> e_proj" 
                       "gluing `` {(i add_2_3, 0)} \<in> e_proj" 
        using add_in add_2_3_def e_proj_aff apply simp
        using add_in add_2_3_def e_proj_aff proj_add_class_inv by auto

      consider
        (111) "(\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3)" |
        (222) "(add_2_3, (x1,y1)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" |
        (333) "(add_2_3, (x1,y1)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x1,y1) = (g \<circ> i) add_2_3))" "(add_2_3, (x1,y1)) \<notin> e'_aff_0"
        using add_in in_aff dichotomy_1 by blast        
      then show ?thesis   
      proof(cases)
        case 111                
        then show ?thesis using assoc_111_ext_add using "33"(1) add_2_3_def assms(1) assms(2) assms(3) by blast
      next
        case 222
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_0" 
          apply(subst (3) prod.collapse[symmetric])
          using 222 e'_aff_0_invariance by fastforce 
        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_ext_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            apply(subst proj_addition_comm)
            using e_proj_1_2 apply(simp,simp)
            apply(subst proj_add_class_inv(1)) 
            using e_proj_1_2 apply simp
            using e_proj_1_2(1) by auto
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)})
                              ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_4,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2) ?g2))"
          proof -
            have "gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_ext_add[symmetric, of "fst (i (x1,y1))" "snd (i (x1,y1))" 0
                                             "fst (i (x2,y2))" "snd (i (x2,y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2)
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            using assms(1) proj_add_class_comm proj_addition_def proj_add_class_inv by auto
          finally have eq2: "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast
          then show ?thesis using eq1 eq2 by blast
        next
          case 2222

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_ext_add_ext_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by auto
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_ext_add_ext_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by auto
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_0_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed  
      next
        case 333
        have assumps: "((x1, y1),add_2_3) \<in> e'_aff_1" 
          using 333(1) e'_aff_1_invariance  add_2_3_def by auto

        consider
          (1111) "(\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2)" |
          (2222) "(add_1_2, (x3,y3)) \<in> e'_aff_0" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" |
          (3333) "(add_1_2, (x3,y3)) \<in> e'_aff_1" "\<not> ((\<exists>g\<in>symmetries. (x3,y3) = (g \<circ> i) add_1_2))" "(add_1_2, (x3,y3)) \<notin> e'_aff_0"
          using add_in_1_2 in_aff dichotomy_1 by blast 
        then show ?thesis 
        proof(cases)
          case 1111 
          then obtain g where g_expr: "g \<in> symmetries" "(x3, y3) = (g \<circ> i) add_1_2" by blast
          then have rot: "\<tau> \<circ> g \<in> rotations" using sym_to_rot assms by blast

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(add_1_2, 0)}) (gluing `` {((g \<circ> i) add_1_2, 0)})"
            using g_expr p_delta_1_2 gluing_ext_add assms(1,2) add_1_2_def by force
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            apply(subst proj_addition_comm)
            using e_proj_1_2(1) g_expr(2) assms(3) apply(simp,simp)
            apply(subst comp_apply,subst (2) prod.collapse[symmetric])
            apply(subst remove_sym)
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst remove_add_sym)
            using e_proj_1_2 rot apply(simp,simp,simp)
            apply(subst prod.collapse, subst (2 4) prod.collapse[symmetric])
            apply(subst proj_addition_comm)
            using e_proj_1_2 rot apply(simp,simp)
            apply(subst proj_add_class_inv(1))
            using e_proj_1_2(1) by auto
          finally have eq1: "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                             tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast

          have "proj_addition ?g1 (proj_addition ?g2 ?g3) = 
                proj_addition ?g1 (proj_addition ?g2 (gluing `` {((g \<circ> i) add_1_2, 0)}))" 
            using g_expr by auto
          also have "... =  proj_addition ?g1
                            (tf'' (\<tau> \<circ> g)
                              (proj_addition (gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)})
                              ?g2))" 
            apply(subst comp_apply,subst (6) prod.collapse[symmetric])
            apply(subst (3) remove_sym) 
            using e_proj_1_2(2) g_expr assms(3) apply(simp,simp,simp)
            apply(subst prod.collapse)
            apply(subst (2) proj_addition_comm) 
            using assms(2) apply simp
            using tf''_preserv_e_proj rot e_proj_1_2(2) apply (metis prod.collapse)
            apply(subst remove_add_sym)
            using assms(2) e_proj_1_2(2) rot apply(simp,simp,simp)
            unfolding add_1_2_def 
            by(subst inverse_rule_4,blast)  
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g)
                              (proj_addition (proj_addition ?ig1 ?ig2) ?g2))"
          proof -
            have "gluing `` {(ext_add (i (x1, y1)) (i (x2, y2)), 0)} = 
                  proj_addition ?ig1 ?ig2"
              using gluing_ext_add[symmetric, of "fst (i (x1, y1))" "snd (i (x1, y1))" 0 
                                             "fst (i (x2, y2))" "snd (i (x2, y2))" 0,
                               simplified prod.collapse] e_proj_0(1,2) p_delta_1_2(2)
              by simp
            then show ?thesis by presburger
          qed
          also have "... = proj_addition ?g1 (tf'' (\<tau> \<circ> g) ?ig1)"
            using cancellation_assoc 
            by (metis assms(2) e_proj_0(1) e_proj_0(2) i.simps i_idemp_explicit)
          also have "... = tf'' (\<tau> \<circ> g) (proj_addition ?g1 ?ig1)"
            using assms(1) e_proj_0(1) proj_addition_comm remove_add_sym rot tf''_preserv_e_proj by fastforce
          also have "... = tf'' (\<tau> \<circ> g) {((1, 0), 0)}"
            using assms(1) proj_add_class_comm proj_addition_def proj_add_class_inv by auto
          finally have eq2: "proj_addition (gluing `` {((x1, y1), 0)})
                              (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)})) = 
                        tf'' (\<tau> \<circ> g) {((1, 0), 0)}" by blast
          then show ?thesis using eq1 eq2 by blast
        next
          case 2222
          
          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
            proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 2222 unfolding e'_aff_0_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst add_ext_ext_ext_assoc)
            apply(simp,simp)
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 2222(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by force+
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps            
            unfolding e'_aff_1_def by(blast,auto)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        next
          case 3333

          have "proj_addition (proj_addition ?g1 ?g2) ?g3 = 
                proj_addition (gluing `` {(ext_add (x1, y1) (x2, y2), 0)}) ?g3"
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2) by simp
          also have "... = gluing `` {(ext_add (ext_add (x1, y1) (x2, y2)) (x3, y3), 0)}"
            apply(subst (2) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            apply(subst prod.collapse)
            using gluing_ext_add p_delta_1_2(1) e_proj_1_2 add_1_2_def assms(1,2,3) apply(simp,simp)
            using 3333 unfolding e'_aff_1_def add_1_2_def by(simp,force)
          also have "... = gluing `` {(ext_add (x1, y1) (ext_add (x2, y2) (x3, y3)), 0)}"
            apply(subst ext_ext_ext_ext_assoc)
            apply(simp,simp) 
            apply(subst prod.collapse[symmetric],subst prod.inject,fast)+
            using p_delta_1_2 p_delta_2_3(1) 3333(1) assumps in_aff
            unfolding e'_aff_0_def e'_aff_1_def delta_def delta'_def 
                      add_1_2_def add_2_3_def e'_aff_def
            by(force)+
          also have "... = proj_addition ?g1 (gluing `` {(ext_add (x2, y2) (x3, y3), 0)})"
            apply(subst (10) prod.collapse[symmetric])
            apply(subst gluing_ext_add)
            using assms(1) e_proj_2_3(1) add_2_3_def assumps
            unfolding e'_aff_1_def by(simp,simp,force,simp)
          also have "... = proj_addition ?g1 (proj_addition ?g2 ?g3)"
            apply(subst gluing_ext_add)
            using assms(2,3) p_delta_2_3(1) by auto
          finally show ?thesis by blast
        qed
      qed 
    qed
  qed
qed

(* idea:

for the above theorem and other similars we could prove a theorem stating that if something holds 
for the aff_0 case then if we modify the hypothesis it holds for the case aff_1 case.

*)

lemma general_assoc:
 assumes "gluing `` {((x1, y1), l)} \<in> e_proj" "gluing `` {((x2, y2), m)} \<in> e_proj" "gluing `` {((x3, y3), n)} \<in> e_proj"
 shows "proj_addition (proj_addition (gluing `` {((x1, y1), l)}) (gluing `` {((x2, y2), m)}))
                      (gluing `` {((x3, y3), n)}) =
        proj_addition (gluing `` {((x1, y1), l)})
                      (proj_addition (gluing `` {((x2, y2), m)}) (gluing `` {((x3, y3), n)}))"
proof -
  let ?t1 = "(proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}))
                                      (gluing `` {((x3, y3), 0)}))"
  let ?t2 = "proj_addition (gluing `` {((x1, y1), 0)})
              (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)}))"
  
  have e_proj_0: "gluing `` {((x1, y1), 0)} \<in> e_proj"
                 "gluing `` {((x2, y2), 0)} \<in> e_proj"
                 "gluing `` {((x3, y3), 0)} \<in> e_proj"
                 "gluing `` {((x1, y1), 1)} \<in> e_proj"
                 "gluing `` {((x2, y2), 1)} \<in> e_proj"
                 "gluing `` {((x3, y3), 1)} \<in> e_proj"
    using assms e_proj_aff by blast+
  have e_proj_add_0: "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}) \<in> e_proj" 
                     "proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)}) \<in> e_proj"
                     "proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 1)}) \<in> e_proj"
                     "proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 1)}) \<in> e_proj" 
                     "proj_addition (gluing `` {((x2, y2), 1)}) (gluing `` {((x3, y3), 0)}) \<in> e_proj"
                     "proj_addition (gluing `` {((x2, y2), 1)}) (gluing `` {((x3, y3), 1)}) \<in> e_proj" 
    using e_proj_0 well_defined proj_addition_def by blast+
    

  have complex_e_proj: "?t1 \<in> e_proj"
                       "?t2 \<in> e_proj"
    using e_proj_0 e_proj_add_0 well_defined proj_addition_def by blast+

  have eq3: "?t1 = ?t2"
    by(subst assoc_with_zeros,(simp add: e_proj_0)+)

  show ?thesis
  proof(cases "l = 0")
    case True
    then have l: "l = 0" by simp
    then show ?thesis 
    proof(cases "m = 0")
      case True
      then have m: "m = 0" by simp
      then show ?thesis 
      proof(cases "n = 0")
        case True
        then have n: "n = 0" by simp
        show ?thesis 
          using l m n assms assoc_with_zeros by simp 
      next
        case False
        then have n: "n = 1" by simp
        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 0)}))
                                 (gluing `` {((x3, y3), 1)}) = tf' (?t1) 
              " 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          by(subst remove_add_tau',auto simp add: e_proj_0 e_proj_add_0)

        have eq2: "proj_addition (gluing `` {((x1, y1), 0)})
                            (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 1)})) =
               tf'(?t2)"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0)+)
          by(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)

        show ?thesis 
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      qed
    next
      case False
      then have m: "m = 1" by simp
      then show ?thesis 
      proof(cases "n = 0")
        case True
        then have n: "n = 0" by simp

        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 1)}))
                                 (gluing `` {((x3, y3), 0)}) = tf'(?t1)"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0)+)
          by(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
        have eq2: "proj_addition (gluing `` {((x1, y1), 0)})
                    (proj_addition (gluing `` {((x2, y2), 1)}) (gluing `` {((x3, y3), 0)})) = 
                  tf'(?t2)"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0)+)
          by(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)

        then show ?thesis
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      next
        case False
        then have n: "n = 1" by simp
        
        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 0)}) (gluing `` {((x2, y2), 1)}))
                   (gluing `` {((x3, y3), 1)}) = ?t1"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0)+)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        have eq2: "proj_addition (gluing `` {((x1, y1), 0)})
             (proj_addition (gluing `` {((x2, y2), 1)}) (gluing `` {((x3, y3), 1)})) = 
                  ?t2" 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0)+)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        then show ?thesis
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      qed
    qed
  next
    case False
    then have l: "l = 1" by simp
  
    then show ?thesis 
    proof(cases "m = 0")
      case True
      then have m: "m = 0" by simp
      then show ?thesis 
      proof(cases "n = 0")
        case True
        then have n: "n = 0" by simp
        
        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 1)}) (gluing `` {((x2, y2), 0)}))
                        (gluing `` {((x3, y3), 0)}) = tf'(?t1)"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0)+)
          by(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)

        have eq2: "proj_addition (gluing `` {((x1, y1), 1)})
           (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 0)})) = 
                  tf'(?t2)" 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          by(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)

        then show ?thesis
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      next
        case False
        then have n: "n = 1" by simp
        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 1)}) (gluing `` {((x2, y2), 0)}))
                     (gluing `` {((x3, y3), 1)}) = ?t1"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0)+)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        have eq2: "proj_addition (gluing `` {((x1, y1), 1)})
           (proj_addition (gluing `` {((x2, y2), 0)}) (gluing `` {((x3, y3), 1)})) = 
                  ?t2" 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        then show ?thesis
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      qed
    next
      case False
      then have m: "m = 1" by simp
      then show ?thesis 
      proof(cases "n = 0")
        case True
        then have n: "n = 0" by simp

        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 1)}) (gluing `` {((x2, y2), 1)}))
                   (gluing `` {((x3, y3), 0)}) = ?t1"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        have eq2: "proj_addition (gluing `` {((x1, y1), 1)})
            (proj_addition (gluing `` {((x2, y2), 1)}) (gluing `` {((x3, y3), 0)})) = 
                  ?t2" 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+) 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        then show ?thesis
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      next
        case False
        then have n: "n = 1" by simp

        have eq1: "proj_addition (proj_addition (gluing `` {((x1, y1), 1)}) (gluing `` {((x2, y2), 1)}))
                  (gluing `` {((x3, y3), 1)}) = tf'(?t1)"
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        have eq2: "proj_addition (gluing `` {((x1, y1), 1)})
     (proj_addition (gluing `` {((x2, y2), 1)}) (gluing `` {((x3, y3), 1)})) = 
                  tf'(?t2)" 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+) 
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau,(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst tf_tau[of _ _ 0,simplified],simp add: e_proj_0)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          apply(subst remove_add_tau',(simp add: e_proj_0 e_proj_add_0)+)
          by(subst tf'_idemp,auto simp add: complex_e_proj) 

        then show ?thesis
          apply(simp add: l m n)
          using eq1 eq2 eq3 by argo
      qed
    qed
  qed
qed

lemma proj_assoc: 
  assumes "x \<in> e_proj" "y \<in> e_proj" "z \<in> e_proj" 
  shows "proj_addition (proj_addition x y) z = proj_addition x (proj_addition y z)"
proof -
  obtain x1 y1 l x2 y2 m x3 y3 n where 
    "x = gluing `` {((x1, y1), l)}"
    "y = gluing `` {((x2, y2), m)}"
    "z = gluing `` {((x3, y3), n)}"
    by (metis assms e_proj_def prod.collapse quotientE)

  then show ?thesis
    using assms general_assoc by force
qed

subsection \<open>Group law\<close>

lemma projective_group_law:
  shows "comm_group \<lparr>carrier = e_proj, mult = proj_addition, one = {((1,0),0)}\<rparr>" 
proof(unfold_locales,simp_all)
  show one_in: "{((1, 0), 0)} \<in> e_proj"
    using identity_proj by auto 

  show comm: "proj_addition x y = proj_addition y x" 
              if "x \<in> e_proj" "y \<in> e_proj" for x y
    using proj_addition_comm that by simp
  
  show id_1: "proj_addition {((1, 0), 0)} x = x" 
              if "x \<in> e_proj" for x
    using proj_add_class_identity that by simp
  
  show id_2: "proj_addition x {((1, 0), 0)} = x"
              if "x \<in> e_proj" for x
     using comm id_1 one_in that by simp

  show "e_proj \<subseteq> Units \<lparr>carrier = e_proj, mult = proj_addition, one = {((1, 0), 0)}\<rparr>"
    unfolding Units_def 
  proof(simp,standard)
    fix x
    assume "x \<in> e_proj"
    then obtain x' y' l' where "x = gluing `` {((x', y'), l')}"
      unfolding e_proj_def
      apply(elim quotientE)
      by auto
    then have "proj_addition (gluing `` {(i (x', y'), l')}) 
                                 (gluing `` {((x', y'), l')}) = 
                                 {((1, 0), 0)}" 
              "proj_addition (gluing `` {((x', y'), l')}) 
                                 (gluing `` {(i (x', y'), l')}) = 
                                 {((1, 0), 0)}"
                  "gluing `` {(i (x', y'), l')} \<in> e_proj"
      using proj_add_class_inv proj_addition_comm \<open>x \<in> e_proj\<close> by simp+
    then show "x \<in> {y \<in> e_proj. \<exists>x\<in>e_proj. proj_addition x y = {((1, 0), 0)} \<and> 
                                            proj_addition y x = {((1, 0), 0)}}"
      using \<open>x = gluing `` {((x', y'), l')}\<close> \<open>x \<in> e_proj\<close> by blast
  qed

  show "proj_addition x y \<in> e_proj"
    if "x \<in> e_proj" "y \<in> e_proj" for x y
    using well_defined that by blast

  show "proj_addition (proj_addition x y) z = proj_addition x (proj_addition y z)"
    if "x \<in> e_proj" "y \<in> e_proj" "z \<in> e_proj" for x y z
    using proj_assoc that by simp
qed

end

end




