theory Example
  imports 
    Polynomial_Interpolation.Lagrange_Interpolation
    Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
    "HOL-Analysis.Complex_Transcendental"
begin

section\<open>Geometric sum\<close>

text\<open>
 First example of periodic modulo k arithmetical function
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

theorem geometric_sum:
 assumes 0: "(k::nat) \<ge> 1"
 defines "g(n::nat) == (\<Sum>m \<in> {0..(k::nat)-1}. exp ((2*pi*m*n*\<i>) / k))"
 shows "\<not> k dvd n \<Longrightarrow> g(n) = 0" and 
       "k dvd n \<Longrightarrow> g(n) = k"
  using case_1 case_2 "0" g_def by auto
 
section\<open>Finite Fourier series\<close>

subsection\<open>Lagrange property\<close>

lemma lagrange_exists:
  assumes d: "distinct (map fst zs_ws)"
  defines e: "(p :: complex poly) == lagrange_interpolation_poly zs_ws"
  shows "degree p \<le> (length zs_ws)-1 \<and>
         (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p x = y)" 
proof -
  from e have 0: "degree p \<le> (length zs_ws - 1)"
    using degree_lagrange_interpolation_poly by auto
  from e d have 1: "\<And> x y. (x,y) \<in> set zs_ws \<Longrightarrow> poly p x = y"
    using lagrange_interpolation_poly by auto
  from 0 1 show ?thesis by auto
qed

lemma lagrange_unique:
  assumes o: "length zs_ws > 0" (* implicit in theorem *)
  assumes d: "distinct (map fst zs_ws)"
  assumes 1: "degree (p1 :: complex poly) \<le> (length zs_ws)-1 \<and>
               (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p1 x = y)"
  assumes 2: "degree (p2 :: complex poly) \<le> (length zs_ws)-1 \<and>
               (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p2 x = y)"
  shows "p1 = p2" 
proof(cases "p1 - p2 = 0")
  case True then show ?thesis by simp
next
  case False
   have "\<And> x. x \<in> set (map fst zs_ws) \<Longrightarrow> poly (p1-p2) x = 0"
   using 1 2 by(auto simp add: field_simps)
   from this d have 3: "card {x. poly (p1-p2) x = 0} \<ge> length zs_ws"
   proof(induction zs_ws)
     case Nil then show ?case by simp
   next
     case (Cons z_w zs_ws)
     from  False poly_roots_finite
     have f: "finite {x. poly (p1 - p2) x = 0}" by blast
     from Cons have "set (map fst (z_w # zs_ws)) \<subseteq> 
                    {x. poly (p1 - p2) x = 0}"
       by auto
     then have i: "card (set (map fst (z_w # zs_ws))) \<le>
              card {x. poly (p1 - p2) x = 0}" 
       using card_mono f by blast
     have "length (z_w # zs_ws) \<le> card (set (map fst (z_w # zs_ws)))"
       using Cons.prems(2) distinct_card by fastforce 
     from this i show ?case by simp 
   qed
   from 1 2 have 4: "degree (p1 - p2) \<le> (length zs_ws)-1" 
     using degree_diff_le by blast
 
   have "p1 - p2 = 0"  
  proof(rule ccontr)
    assume "p1 - p2 \<noteq> 0"
    then have "card {x. poly (p1-p2) x = 0} \<le> degree (p1-p2)"
      using poly_roots_degree by blast
    then have "card {x. poly (p1-p2) x = 0} \<le> (length zs_ws)-1"
      using 4 by auto
    then show "False" using 3 o by linarith
  qed
  then show ?thesis by simp 
qed

lemma lagrange:
 "length zs_ws > 0 \<Longrightarrow>
  distinct (map fst zs_ws) \<Longrightarrow>
  (\<exists>! (p :: complex poly).
    degree p \<le> (length zs_ws)-1 \<and>
    (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p x = y))"
  using lagrange_exists lagrange_unique by blast

subsection\<open>Roots of unit\<close>

lemma roots_of_unit_equal:
 assumes w: "k > 0"
 defines "f  == (\<lambda> m k. exp (-((2*m/(k::int))*pi)*\<i>))"
 assumes e: "f (i::int) k = f (j::int) k"
 shows "i mod k = j mod k"
proof -
  let ?arg1 = "-((2*i/k)*pi)*\<i>"
  let ?arg2 = "-((2*j/k)*pi)*\<i>"
  from e f_def
  have "exp ?arg1 = exp ?arg2" by auto
  from this exp_eq 
  obtain n :: int where "?arg1 = ?arg2 +(2 *n*pi)*\<i>" by blast
  then have e1: "?arg1 - ?arg2 = 2*n*pi*\<i>" by simp
  have e2: "?arg1 - ?arg2 = 2*(j-i)*(1/k)*pi*\<i>"
    by(auto simp add: algebra_simps)
  from e1 e2 have "2*n*pi*\<i> = 2*(j-i)*(1/k)*pi*\<i>" by simp
  then have "2*n*pi*\<i>*\<i> = 2*(j-i)*(1/k)*pi*\<i>*\<i>"
    by(auto simp add: field_simps)
  then have "2*n*pi*(-1) = 2*(j-i)*(1/k)*pi*(-1)"
    using i_squared complex_i_not_zero 
    by (metis mult_cancel_right of_real_eq_iff)
  then have "2*n*pi = 2*(j-i)*(1/k)*pi" by simp
  then have "2*n = 2*(j-i)*(1/k)"
    using mult_cancel_right pi_neq_zero by blast
  then have "n = (j-i)*(1/k)" by linarith
  then have "n*k = j-i" 
    using w apply(auto simp add: field_simps)
    using of_int_eq_iff by fastforce
  then show ?thesis by algebra
qed

lemma div_minus:
  fixes n :: int
  assumes n_bounds: "0 \<le> n \<and> n < k"
  assumes m_bounds: "0 \<le> m \<and> m < k"
  assumes r_bounds: "0 \<le> r \<and> r < k"
  shows "k dvd (n-r) \<longleftrightarrow> n = r"
proof(rule iffI) 
 assume dvd: "k dvd (n-r)"
 then show "n = r"
 proof(cases "n > r")
  case True then show ?thesis 
   using dvd n_bounds r_bounds zdvd_imp_le by force
 next
  case False
   have rev: "k dvd (n-r) \<longleftrightarrow> k dvd (r-n)"
    by (simp add: dvd_diff_commute)
   from this False have "r = n"
    using dvd n_bounds r_bounds zdvd_imp_le by fastforce
   then show ?thesis by simp        
 qed
next
  assume "n = r" then show "k dvd n - r" by simp
qed

lemma extended_altdef:
 assumes gr: "k \<ge> degree p"  
 shows "\<exists> a. poly p (z::complex) = (\<Sum>i\<le>k. a(i) * z ^ i)"
proof -
  have 1: "poly p z = (\<Sum>i\<le>degree p. coeff p i * z ^ i)"
    using poly_altdef[of p z] by simp
  have "k \<ge> degree p \<Longrightarrow> poly p z = (\<Sum>i\<le>k. coeff p i * z ^ i)"
  proof(induction k)
    case 0 then show ?case  by(simp add: poly_altdef) 
  next
    case (Suc k) 
    then show ?case
      using "1" le_degree not_less_eq_eq by fastforce
  qed  
  then show ?thesis using gr by blast
qed

lemma roots_of_unit:
  assumes "length ws > 0"
  defines "k == length ws"
  shows "
  \<exists>! (p :: complex poly).
   (degree p \<le> k - 1) \<and>
   (\<forall> m. (ws ! m) = poly p (exp (-(2*m/(k::int))*pi*\<i>)))
    \<and> 
   (\<forall> n. coeff p n = (1/k)*(\<Sum>m < k. (w ! m)* exp (-(2*pi*m*n/k)*\<i>)))"
proof -
  let ?k = "length ws"
  let ?t = "[0..<?k]"  
  let ?f = "\<lambda> m. exp (-(2*m/(?k::int))*pi*\<i>)"
  let ?z = "map (\<lambda> m. ?f m)  ?t"
  {
  fix i j
  assume b: "0 \<le> i \<and> i < ?k \<and> 0 \<le> j \<and> j < ?k \<and> i \<noteq> j"
  have "?z ! i \<noteq> ?z ! j"
  proof -
    {assume c: "?z ! i = ?z ! j"
    from b have 1: "?z ! i = exp (-(2*i/(?k::int))*pi*\<i>)" by simp
    from b have 2: "?z ! j = exp (-(2*j/(?k::int))*pi*\<i>)" by simp
    from 1 2 c have 3: "exp (-(2*i/(?k::int))*pi*\<i>) = exp (-(2*j/(?k::int))*pi*\<i>)"
      by simp
    from this roots_of_unit_equal[of ?k i j] assms
    have "int i mod int (length ws) = int j mod int (length ws)"
      by (simp)
    from this assms have "i mod ?k = j mod ?k" 
      using b by auto
    from this b have "i = j" by auto
    from this b have  "False" by auto}
    then show ?thesis by blast
  qed
  }
  then have d: "distinct ?z" 
    by (simp add: distinct_conv_nth)
  let ?zs_ws = "zip ?z ws"
  from lagrange[of "?zs_ws"] have 
    "\<exists>!p. degree p \<le> ?k - 1 \<and>
       (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly p x = y) "
    using d assms by auto 
  then obtain p where 
    ps: "degree p \<le> ?k - 1 \<and>
     (\<forall>z w. (z, w) \<in> set ?zs_ws \<longrightarrow> poly p z = w)" by blast
  fix z w 
  fix m :: int and r :: int
  assume a2: "m \<ge> 0 \<and> r \<ge> 0 \<and> m < k \<and> r < k"
  assume a1: "(z, w) \<in> set ?zs_ws"
  (*then have "\<exists> a. poly p z = (\<Sum>i<?k. a(i) * z ^ i)"
    using poly_altdef*)
  from ps a1 have "w = poly p z" by simp
  then have "w*?f (m*r) = (poly p z)*?f (m*r)" by simp
  
    
  from ps have "poly p z = w"
qed
  

end