theory Example
  imports 
    Polynomial_Interpolation.Lagrange_Interpolation
    Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
    "HOL-Analysis.Complex_Transcendental"
begin

section\<open>Roots of unity\<close>

definition "unity_root k n = 
            cis (2 * pi * of_int n / of_nat k)"

lemma unity_k_0: "unity_root k 0 = 1"
  unfolding unity_root_def
  by simp

lemma unity_0_n: "unity_root 0 n = 1"
 unfolding unity_root_def
  by simp

lemma unity_exp: "unity_root k n = exp ((2*pi*n/k)* \<i>)"
  using unity_root_def cis_conv_exp mult.commute by metis

lemma unity_mod: "unity_root k n = unity_root k (n mod k)"
proof(cases "k = 0")
  case True then show ?thesis by simp
next
  case False
  obtain q :: int  where "n = q*k + (n mod k)" 
    using div_mult_mod_eq by metis
  then have "n/k = q + (n mod k)/k"
    using False
    by(auto simp add: divide_simps,
       metis of_int_add of_int_mult of_int_of_nat_eq)
  then have "(2*pi*n/k) = 2*pi*q + (2*pi*(n mod k)/k)"
    using False by(auto simp add: field_simps)
  then have "(2*pi*n/k)*\<i> = 2*pi*q*\<i> + (2*pi*(n mod k)/k)*\<i>" (is "?l = ?r1 + ?r2")
    by(auto simp add: algebra_simps)
  then have "exp ?l = exp ?r2"
    using exp_plus_2pin by (simp add: exp_add mult.commute)
  then show ?thesis 
    using unity_root_def unity_exp by simp
qed

lemma unity_mod_nat: "unity_root k n = unity_root k (nat (n mod k))"
  using unity_mod 
  by (metis Euclidean_Division.pos_mod_sign add_0_left add_divide_eq_if_simps(1) int_nat_eq linorder_neqE_linordered_idom linorder_not_le nat_int of_nat_eq_0_iff unity_root_def) 

lemma unity_dvd:
  fixes k n :: nat
  assumes "k > 0" 
  shows "(unity_root k n = 1) \<longleftrightarrow> (k dvd n)"
proof -
  have "unity_root k n = exp ((2*pi*n/k)* \<i>)"
    using unity_exp by simp
  also have "exp ((2*pi*n/k)* \<i>) = 1 \<longleftrightarrow> k dvd n"
    using complex_root_unity_eq_1[of k n] assms
    by(auto simp add: algebra_simps)
  finally show ?thesis by simp
qed

lemma unity_pow: "(unity_root k n)^m = unity_root k (n*m)"
  using unity_root_def
  by (simp add: Complex.DeMoivre linordered_field_class.sign_simps(6) mult.commute)

lemma unity_prod: "unity_root k m* unity_root k n = unity_root k (m+n)"
  using unity_exp
  by(auto simp add: algebra_simps add_divide_distrib mult_exp_exp)

section\<open>Geometric sum\<close>

text\<open>
 First example of periodic modulo k arithmetical function
\<close>


lemma exp_dvd_nat:
  fixes n k :: nat
  assumes "k > 0"
  shows "exp ((2*pi*n/k) * \<i>) = 1 \<longleftrightarrow> k dvd n"
proof(rule iffI)
  assume 1: "exp ((2*pi*n/k)*\<i>) = 1"
  from this cis.sel cis_conv_exp have "cos (2*pi*n/k) = 1" 
    by (metis complex_Re_numeral mult.commute numeral_One)
  then obtain l::int where "2*pi*n/k = 2*pi*l"
    using cos_one_2pi_int by auto
  then have "n = k * l" 
    apply(auto simp add: field_simps assms) 
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

(* 
 An example of a theorem deduced from the version for nats
 taking advantage of exponential's periodicity.
*)
lemma exp_dvd_int:
  fixes n :: int and  k :: nat
  assumes "k > 0"
  shows "unity_root k n = 1 \<longleftrightarrow> k dvd n"
proof - 
  have "unity_root k n = unity_root k (nat (n mod k))"
    using unity_mod_nat by blast
  also have "unity_root k (nat (n mod k)) = 1 \<longleftrightarrow> k dvd (nat (n mod k))"
    using assms exp_dvd_nat
    by (metis of_int_of_nat_eq unity_exp)
  also have "k dvd (nat (n mod k)) \<longleftrightarrow> k dvd n"
    using assms
    by (metis Euclidean_Division.pos_mod_sign dvd_mod_iff dvd_refl int_dvd_int_iff int_nat_eq of_nat_0_less_iff)
  finally show ?thesis by simp
qed

definition "geometric_sum k n = (\<Sum>m\<le>k-1. unity_root k (n* of_nat m))"

lemma geo_0_n: "geometric_sum 0 n = 1"
  unfolding geometric_sum_def
  using unity_0_n by simp
  
  

lemma gs_case_1:
  fixes k :: nat and n :: int
  assumes gr: "k \<ge> 1"
  assumes dvd: "k dvd n"
  shows "geometric_sum k n = k"
proof -
  let ?x = "unity_root k n"
  have unit: "?x = 1" using dvd gr exp_dvd_int by auto
  have exp: "\<And> m. ?x^m = unity_root k (n*m)"
    using unity_pow by simp
  have "geometric_sum k n = (\<Sum>m\<le>k-1. unity_root k (n*m))" 
    using geometric_sum_def by simp 
  also have "... = (\<Sum>m\<le>k-1. ?x^m)"
    using exp  by auto
  also have "... = (\<Sum>m\<le>k-1. 1)" 
    using unit by simp
  also have "... = k" 
    using gr by(induction k, auto)
  finally show "geometric_sum k n = k" by simp
qed                       

lemma gs_case_2:
  fixes k :: nat and n :: int
  assumes gr: "k \<ge> 1"
  assumes dvd: "\<not> k dvd n"
  shows "geometric_sum k n = 0"
proof -
  let ?x = "unity_root k n"
  have "?x \<noteq> 1" using dvd gr exp_dvd_int by auto
  then have "(?x^k - 1)/(?x - 1) = (\<Sum> m\<le>k-1. ?x^m)"
      using geometric_sum[of ?x k] gr
      by(auto simp add: divide_simps,
         metis Suc_le_lessD Suc_pred lessThan_Suc_atMost)
  then have sum: "geometric_sum k n = (?x^k - 1)/(?x - 1)"
    using geometric_sum_def unity_pow by simp
  have "?x^k = 1" 
    using gr exp_dvd_int unity_pow by simp
  then show ?thesis using sum by auto
qed

theorem geometric_sum:
 fixes k :: nat and n :: int
 assumes gr: "k \<ge> 1"
 shows "\<not> k dvd n \<Longrightarrow> geometric_sum k n = 0" and 
       "  k dvd n \<Longrightarrow> geometric_sum k n = k"
  using gs_case_1 gs_case_2 gr by blast+

corollary geometric_sum_periodic:
  fixes k :: nat and n :: int
 assumes gr: "k \<ge> 1"
 shows "geometric_sum k n = geometric_sum k (n+k)"
proof(cases "k dvd n")
  case True then show ?thesis 
    using gr gs_case_1 by auto
next
  case False then show ?thesis 
    using gr gs_case_2 by auto
qed

lemma geometric_sum_div:
  fixes r :: int
  assumes "k \<ge> 1"
  assumes "-k < r \<and> r < k"
  shows "geometric_sum k r \<noteq> 0 \<longleftrightarrow> r = 0"
proof
  assume "geometric_sum k r \<noteq> 0"
  then have "k dvd r" using geometric_sum assms by blast
  then show "r = 0" using assms(2) 
    using dvd_imp_le_int by force
next
  assume "r = 0"
  then have "k dvd r" by auto
  then have "geometric_sum k r = k" 
    using assms(1) geometric_sum by blast
  then show "geometric_sum k r \<noteq> 0" using assms(1) by simp
qed

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

(* see complex_root_unity_eq *)
lemma roots_of_unit_equal:
 assumes gr: "k > 0"
 assumes eq: "unity_root k i = unity_root k j"
 shows "i mod k = j mod k"
proof - 
  let ?arg1 = "(2*pi*i/k)* \<i>"
  let ?arg2 = "(2*pi*j/k)* \<i>"
  from eq unity_exp have "exp ?arg1 = exp ?arg2" by simp
  from this exp_eq 
  obtain n :: int where "?arg1 = ?arg2 +(2*n*pi)*\<i>" by blast
  then have e1: "?arg1 - ?arg2 = 2*n*pi*\<i>" by simp
  have e2: "?arg1 - ?arg2 = 2*(i-j)*(1/k)*pi*\<i>"
    by(auto simp add: algebra_simps)
  from e1 e2 have "2*n*pi*\<i> = 2*(i-j)*(1/k)*pi*\<i>" by simp
  then have "2*n*pi*\<i>*\<i> = 2*(i-j)*(1/k)*pi*\<i>*\<i>"
    by(auto simp add: field_simps)
  then have "2*n*pi*(-1) = 2*(i-j)*(1/k)*pi*(-1)"
    using i_squared complex_i_not_zero 
    by (metis mult_cancel_right of_real_eq_iff)
  then have "2*n*pi = 2*(i-j)*(1/k)*pi" by simp
  then have "2*n = 2*(i-j)*(1/k)"
    using mult_cancel_right pi_neq_zero by blast
  then have "n = (i-j)*(1/k)" by linarith
  then have "n*k = i-j" 
    using gr apply(auto simp add: divide_simps)
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

lemma geometric_sum_div:
  fixes r :: int
  assumes "0 \<le> r \<and> r < k"
  assumes "0 \<le> n \<and> n < k"
  shows "geometric_sum k (n-r) \<noteq> 0 \<longleftrightarrow> n = r"
proof - 
  have ineq: "0 \<le> n-r \<and> n-r< k"
    using assms 
  have "k dvd (n-r) \<longleftrightarrow> n = r"
  proof 
    assume "k dvd n - r"
    then show "n = r"
     proof(cases "n > r")
       case True then show ?thesis 
         using \<open>k dvd n - r\<close> ineq by auto
     next
       case False
       have rev: "k dvd (n-r) \<longleftrightarrow> k dvd (r-n)"
         using dvd_diff_commute sorry
       thm dvd_diff_commute
   from this False have "r = n"
    using dvd n_bounds r_bounds zdvd_imp_le by fastforce
   then show ?thesis by simp        
 qed
  qed
qed

lemma extended_altdef:
 assumes gr: "k \<ge> degree p"  
 shows "poly p (z::complex) = (\<Sum>i\<le>k. coeff p i * z ^ i)"
proof -
  {fix z
  have 1: "poly p z = (\<Sum>i\<le>degree p. coeff p i * z ^ i)"
    using poly_altdef[of p z] by simp
  have "poly p z = (\<Sum>i\<le>k. coeff p i * z ^ i)" 
    using gr
  proof(induction k)
    case 0 then show ?case by(simp add: poly_altdef) 
  next
    case (Suc k) 
    then show ?case
      using "1" le_degree not_less_eq_eq by fastforce
  qed}  
  then show ?thesis using gr by blast 
qed

lemma distinct_z: 
  "distinct (map (\<lambda> m. unity_root k m) [0..<k])" 
proof -
  let ?z = "map (\<lambda> m. unity_root k m) [0..<k]"
  {
  fix i j
  assume b: "0 \<le> i \<and> i < k \<and> 0 \<le> j \<and> j < k \<and> i \<noteq> j"
  have "?z ! i \<noteq> ?z ! j"
  proof -
    {assume c: "?z ! i = ?z ! j"
    from b have 1: "?z ! i = unity_root k i" by simp
    from b have 2: "?z ! j = unity_root k j" by simp
    from 1 2 c have "unity_root k i = unity_root k j" by simp
    from this roots_of_unit_equal[of k i j] b
    have "i mod k = j mod k" by simp
    from this b have "i = j" by auto
    from this b have  "False" by auto}
    then show ?thesis by blast
  qed
  }
  then show ?thesis by (simp add: distinct_conv_nth)
qed

lemma roots_of_unit:
  assumes "length ws > 0"
  defines "k == length ws"
  shows "
  \<exists>! (p :: complex poly).
   (degree p \<le> k - 1) \<and>
   (\<forall> m. (ws ! m) = poly p (unity_root k m))
    \<and> 
   (\<forall> n. coeff p n = (1/k)*(\<Sum>m < k. (w ! m)* (unity_root k (-n*m))))"
proof -  
  let ?z = "map (\<lambda> m. unity_root k m) [0..<k]" 
  have d: "distinct ?z" using distinct_z k_def by blast
  
  let ?zs_ws = "zip ?z ws"
  from lagrange[of "?zs_ws"] have 
    "\<exists>!p. degree p \<le> k - 1 \<and>
       (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly p x = y) "
    using d assms by auto 
  then obtain p where 
    ps: "degree p \<le> k - 1 \<and>
     (\<forall>z w. (z, w) \<in> set ?zs_ws \<longrightarrow> poly p z = w)" by blast
  then have deg_ineq: "degree p \<le> k - 1" 
        and interp: "(\<forall>z w. (z, w) \<in> set ?zs_ws \<longrightarrow> poly p z = w)"
    by(blast,blast)
  obtain a where pexpr: "\<And> z. poly p z = (\<Sum>i\<le>k-1. a(i) * z ^ i)"
    using extended_altdef deg_ineq by blast

  have "\<And> m r. m \<ge> 0 \<and> r \<ge> 0 \<and> m < k \<and> r < k \<Longrightarrow> 
        (\<And> n. (unity_root k m)^n = unity_root k (m*n))"
    by (simp add: unity_pow)   

  have exp_distr: "\<And> m n r. unity_root k (m*n)* unity_root k (-m*r) = 
                             unity_root k (m*(n-r))"
    using unity_prod by(simp add: algebra_simps)

  {
    fix m r :: int
    assume bounds: "m \<ge> 0 \<and> r \<ge> 0 \<and> m < k \<and> r < k"
    then have unit: "?z ! nat m = unity_root k m" by auto
    from bounds have "(?z ! nat m, ws ! nat m) \<in> set ?zs_ws"
      using fst_conv in_set_zip bounds
      by (metis diff_zero k_def length_map length_upt nat_less_iff snd_conv)
    then have "(ws ! nat m) =  poly p (?z ! nat m)"
      using interp by simp  
    then have "(ws ! nat m) = (\<Sum>n\<le>k-1. a(n) * (unity_root k m) ^ n)"
      using unit pexpr by auto
    then have "((ws ! nat m)*unity_root k (-m*r)) =
           (\<Sum>n\<le>k-1. a(n) * (unity_root k m) ^ n)*unity_root k (-m*r)" 
      by auto
    also have "... = (\<Sum>n\<le>k-1. a(n) * (unity_root k (m*n)))*unity_root k (-m*r)"  
      using unity_pow by simp
    also have "... = (\<Sum>n\<le>k-1. (a(n)*unity_root k (m*n))*unity_root k (-m*r))"  
      by (simp add: sum_distrib_right)
    also have "... = (\<Sum>n\<le>k-1. a(n)*(unity_root k (m*n)*unity_root k (-m*r)))"
      by (simp add: mult.assoc)   
    also have "... = (\<Sum>n\<le>k-1. a(n) * (unity_root k (m*(n-r))))" 
      using exp_distr by simp
    finally have 
       "((ws ! nat m)*unity_root k (-m*r)) = 
         (\<Sum>n\<le>k-1. a(n) * (unity_root k (m*(n-r))))"
      by argo
  }
  note summand = this

  fix r :: int
  assume r_bound: "r \<ge> 0 \<and> r < k"
  {   
    from summand have
      "\<And> m. m \<ge> 0  \<and> m < k \<Longrightarrow> 
         ((ws ! nat m)*unity_root k (-m*r)) = 
         (\<Sum>n\<le>k-1. a(n) * (unity_root k (m*(n-r))))"
      by (meson r_bound of_nat_0_le_iff of_nat_less_iff)
    then have "(\<Sum>m\<le>k-1.(ws ! nat m)*unity_root k (-m*r)) = 
           (\<Sum>m\<le>k-1. (\<Sum>n\<le>k-1. a(n) * (unity_root k (m*(n-r)))))"
      using r_bound by auto
    also have "... = (\<Sum>n\<le>k-1.(\<Sum>m\<le>k-1. a(n)*(unity_root k (m*(n-r)))))"
      using sum.swap by fast
    also have "... = (\<Sum>n\<le>k-1.a(n)*(\<Sum>m\<le>k-1. (unity_root k (m*(n-r)))))"
      by (simp add: vector_space_over_itself.scale_sum_right)
    also have  
      "... = 
      (\<Sum>n\<le>k-1.a(n)*(\<Sum>m\<le>k-1. (unity_root k (m*(n-r)))))"
      by argo
    also have 
      "... = (\<Sum>n\<le>k-1.a(n)*geometric_sum k (n-r))"
      using geometric_sum_def 
      by(simp add: algebra_simps)
  }
  note macro = this

  have "(\<Sum>n\<le>k-1.a(n)*geometric_sum k (n-r)) = a(k)*k"
  proof -
    {fix n
    assume n_bound: "n \<ge> 0 \<and> n < k"
    have "geometric_sum k (n-r) \<noteq> 0 \<longleftrightarrow> n = r"
      using  k_def assms geometric_sum_div[of k "n-r"]
      using n_bound r_bound by auto}
  note zeros = this
  term "sum.F"
  have k_pos: "k > 0" using assms by simp
  have
    "(\<Sum>n\<le>k-1.a(n)*geometric_sum k (n-r))= 
      a(nat r)*geometric_sum k 0"
    using k_pos
    apply(induction "k" arbitrary: r a )
     apply simp
    apply simp
  qed


qed
  

end