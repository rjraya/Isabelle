theory Example
  imports 
    Polynomial_Interpolation.Lagrange_Interpolation
    Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
begin

section\<open>Geometric sum\<close>

text\<open>
 First example of peridic modulo k arithmetical function
\<close>

lemma exp_dvd:
  "k > 0 \<Longrightarrow> exp ((2*pi*(n::nat)/(k::nat)) * \<i>) = 1 \<longleftrightarrow> k dvd n"
proof(rule iffI)
  (* e^(ix) = cos x + i sin x *)
  assume 0:"k > 0"
  assume 1: "exp ((2*pi*n/k)*\<i>) = 1"
  from this cis.sel cis_conv_exp have "cos (2*pi*n/k) = 1" 
    by (metis complex_Re_numeral mult.commute numeral_One)
  then obtain l::int where "2*pi*n/k = 2*pi*l"
    using cos_one_2pi_int by auto
  then have "n = k * l" 
    apply(auto simp add: field_simps "0") 
    using of_int_eq_iff by fastforce
  then show "k dvd n" 
    using int_dvd_int_iff by fastforce
next
  assume "k dvd n"
  then obtain l :: nat where "exp ((2*pi*n/k)*\<i>) = exp (2*pi*l*\<i>)" 
    by (metis real_of_nat_div times_divide_eq_right)
  then show "exp ((2*pi*n/k)*\<i>) = 1"
    by (auto simp add: field_simps,
        metis exp_of_nat_mult exp_two_pi_i' exp_zero mult_eq_0_iff semiring_normalization_rules(19))
qed

lemma case_1:
  assumes 0: "(k::nat) \<ge> 1"
  assumes 1: "k dvd n"
  assumes 2: "g(n::nat) = (\<Sum>m \<in> {0..(k::nat)-1}. exp ((2*pi*m*n*\<i>) / k))"
  shows "g(n) = k"
proof -
  let ?x = "exp ((2*pi*n*\<i>) / k)"
  have "\<And> m. exp ((2*pi*m*n*\<i>) / k) = (?x)^m"
    by (auto simp add: field_simps,
        metis (no_types, hide_lams) exp_of_nat_mult semiring_normalization_rules(19) times_divide_eq_right)
  from this 2 have 3: "g(n) = (\<Sum>m \<in> {0..k-1}. (?x)^m)" by simp
  have "?x = 1" using exp_dvd 0 1 by simp
  from 3 this have "g(n) = (\<Sum>m \<in> {0..k-1}. 1)" by auto
  then show ?thesis  
    by (auto simp add: field_simps,
        metis "0" One_nat_def Suc_diff_le diff_Suc_1 of_nat_Suc)
qed                       

lemma case_2:
  assumes 0: "(k::nat) \<ge> 1"
  assumes 1: "\<not> k dvd n"
  assumes 2: "g(n::nat) = (\<Sum>m \<in> {0..(k::nat)-1}. exp ((2*pi*m*n*\<i>) / k))"
  shows "g(n) = 0"
proof -
  let ?x = "exp ((2*pi*n*\<i>) / k)"
  from exp_dvd 0 1 have "?x \<noteq> 1" by simp
  then have 3: "(?x^k - 1)/(?x - 1) = (\<Sum> m \<in> {0..k-1}. ?x^m)"
      using geometric_sum[of ?x k]
      by (metis One_nat_def Suc_pred atLeast0AtMost divide_eq_0_iff 
                exp_zero lessThan_Suc_atMost neq0_conv of_nat_eq_0_iff)
  then have "\<And> m. exp ((2*pi*m*n*\<i>) / k) = (?x)^m"
    by (auto simp add: divide_simps,
        metis (mono_tags, lifting) exp_of_nat_mult mult.left_commute 
              semiring_normalization_rules(17) times_divide_eq_right)
  from this 2 3 have 4: "g(n) = (?x^k - 1)/(?x - 1)"
    by simp
  from 0 have "?x^k = exp (2*pi*n*\<i>)"
    using exp_divide_power_eq linorder_not_le by blast
  then have "?x^k = 1" 
    by (metis exp_of_nat2_mult exp_two_pi_i' mult.commute of_nat_numeral
              of_real_mult of_real_of_nat_eq power_one semiring_normalization_rules(19))
  from this 4 show ?thesis by auto
qed

section\<open>Finite Fourier series\<close>

thm fundamental_theorem_of_algebra
lemma "
 distinct xs \<Longrightarrow>
 (\<forall> x \<in> set xs. poly p x = 0) \<Longrightarrow>
 degree p \<le> (length xs) - 1 \<Longrightarrow>
 p = 0
"


lemma lagrange:
 "distinct (map fst zs_ws) \<Longrightarrow>
  (\<exists>! (p :: complex poly).
    degree p \<le> (length zs_ws)-1 \<and>
    (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p x = y))"
proof -
  let ?p = "lagrange_interpolation_poly zs_ws"
  have 0: "degree ?p \<le>
        (length zs_ws - 1)"
    using degree_lagrange_interpolation_poly by auto
  assume a1: "distinct (map fst zs_ws)"
  then have 1: "\<And> x y. (x,y) \<in> set zs_ws \<Longrightarrow> poly ?p x = y"
    using lagrange_interpolation_poly by auto
  fix q
  assume a2: "
    (degree q \<le> (length zs_ws)-1 \<and>
    (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly q x = y))"
  have "\<And> x y. (x,y) \<in> set zs_ws \<Longrightarrow> poly (?p-q) x = 0"
    using 1 a2
    by(auto simp add: field_simps)
  then have "poly (?p - q) = poly 0"
    using 1 a1 a2
   
  then have "q = lagrange_interpolation_poly zs_ws"
    
qed

end