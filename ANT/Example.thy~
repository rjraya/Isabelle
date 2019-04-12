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

lemma geo_k_0: "k > 0 \<Longrightarrow> geometric_sum k 0 = k"  
  unfolding geometric_sum_def
  by(simp add: unity_k_0)
  

lemma gs_case_1:
  fixes k :: nat and n :: int
  assumes gr: "k \<ge> 1"
  assumes dvd: "k dvd n"
  shows "geometric_sum k n = k"
proof -
  let ?x = "unity_root k n"
  have unit: "?x = 1" using dvd gr exp_dvd_int by auto
  have exp: "?x^m = unity_root k (n*m)" for m
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
  from e d have 1: 
    "poly p x = y" if "(x,y) \<in> set zs_ws" for x y 
    using that lagrange_interpolation_poly by auto
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
  have "poly (p1-p2) x = 0" if "x \<in> set (map fst zs_ws)" for x
   using 1 2 that by(auto simp add: field_simps)
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

lemma sum_eq_ineq: "n > 0 \<Longrightarrow> (\<Sum>i\<le>n-1. f i) = (\<Sum>i<n. f i)" 
  for n :: nat and f :: "nat \<Rightarrow> complex"
  by (metis Suc_diff_1 lessThan_Suc_atMost)

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

definition fourier_poly :: "complex list \<Rightarrow> complex poly" where
"fourier_poly ws =
  (let k = length ws
    in  poly_of_list [1 / k * (\<Sum>m<k. ws ! m * unity_root k (-n*m)).
      n \<leftarrow> [0..<k]])"

lemma degree_poly: "degree (poly_of_list ws) \<le> length ws - 1"
  by(induction ws, auto,
     metis Poly.simps(1) Suc_pred length_greater_0_conv not_less_eq_eq)

lemma degree_fourier: "degree (fourier_poly ws) \<le> length ws - 1"
  using fourier_poly_def degree_poly
  by (metis (no_types, lifting) diff_zero length_map length_upt)
  
lemma coeff_fourier: 
  assumes "n < length ws"
  defines "k == length ws"
  shows "coeff (fourier_poly ws) n = 
         (1/k) * (\<Sum>m < k. ws ! m * unity_root k (-n*m))"
  unfolding fourier_poly_def 
  apply(simp add: Let_def)
  unfolding nth_default_def
  using degree_fourier assms(1) k_def by auto

lemma interpolate_fourier:
  fixes m :: int
  assumes "0 \<le> m \<and> m < k"
  assumes "m < length ws"
  defines "k == length ws"
  shows "poly (fourier_poly ws) (unity_root k m) = ws ! (nat m)"
proof -
  have distr: "
   (\<Sum>j<length ws. ws ! j * unity_root k (-i*j))*(unity_root k (m*i)) = 
   (\<Sum>j<length ws. ws ! j * unity_root k (-i*j)*(unity_root k (m*i)))"
   for i
  using sum_distrib_right[of "\<lambda> j. ws ! j * unity_root k (-i*j)" 
                            "{..<k}" "(unity_root k (m*i))"] 
  using k_def by blast

  {fix j i :: nat
   have "unity_root k (-i*j)*(unity_root k (m*i)) = unity_root k (-i*j+m*i)"
     using unity_prod[of k "-i*j" "m*i"]
     by simp
   also have "... = unity_root k (i*(m-j))"
     by(simp add: algebra_simps)
   finally have "unity_root k (-i*j)*(unity_root k (m*i)) = unity_root k (i*(m-j))"
     by simp
   then have "ws ! j * unity_root k (-i*j)*(unity_root k (m*i)) = 
              ws ! j * unity_root k (i*(m-j))"
     by auto
 } note prod = this

 have zeros: 
   "(geometric_sum k (m-j) \<noteq> 0 \<longleftrightarrow> m = j)
     " if "j \<ge> 0 \<and> j < k"  for j
   using  k_def that assms geometric_sum_div[of _ "m-j"] by simp
  then have sum_eq:
    "(\<Sum>j\<le>k-1. ws ! j * geometric_sum k (m-j)) = 
          (\<Sum>j\<in>{nat m}.  ws ! j * geometric_sum k (m-j))"
    using assms(1) by(intro sum.mono_neutral_right,auto)
  
  have "poly (fourier_poly ws) (unity_root k m) = 
        (\<Sum>i\<le>k-1. coeff (fourier_poly ws) i * (unity_root k m) ^ i)"
    using degree_fourier[of ws] k_def
          extended_altdef[of "fourier_poly ws" "k-1" 
                             "unity_root k m"]
    by blast
  also have "... = (\<Sum>i<k. coeff (fourier_poly ws) i * (unity_root k m) ^ i)"
    using sum_eq_ineq assms(1) by auto
  also have "... = (\<Sum>i<k. 1 / k *
    (\<Sum>j<k. ws ! j * unity_root k (-i*j)) * (unity_root k m) ^ i)"
    using coeff_fourier[of _ ws] k_def by auto
  also have "... = (\<Sum>i<k. 1 / k *
    (\<Sum>j<k. ws ! j * unity_root k (-i*j))*(unity_root k (m*i)))"
    using unity_pow  by auto   
  also have "... = (\<Sum>i<k. 1 / k *
    (\<Sum>j<k. ws ! j * unity_root k (-i*j)*(unity_root k (m*i))))"
    using distr k_def by simp
  also have "... = (\<Sum>i<k. 1 / k * 
    (\<Sum>j<k. ws ! j * unity_root k (i*(m-j))))"
    using prod by presburger
  also have "... = 1 / k * (\<Sum>i<k.  
    (\<Sum>j<k. ws ! j * unity_root k (i*(m-j))))"
    by (simp add: sum_distrib_left)
  also have "... = 1 / k * (\<Sum>j<k.  
    (\<Sum>i<k. ws ! j * unity_root k (i*(m-j))))"
    using sum.swap by fastforce
  also have "... = 1 / k * (\<Sum>j<k. ws ! j * 
    (\<Sum>i<k. unity_root k (i*(m-j))))"
    by (simp add: vector_space_over_itself.scale_sum_right)
  also have "... = 1 / k * (\<Sum>j<k. ws ! j * 
    (\<Sum>i\<le>k-1. unity_root k (i*(m-j))))"
    using sum_eq_ineq assms 
    by (smt of_nat_0_less_iff sum.cong) (* fix *)
  also have "... = 1 / k * (\<Sum>j<k. ws ! j * geometric_sum k (m-j))"
    using geometric_sum_def 
    by(simp add: algebra_simps)
  also have "... = 1 / k * (\<Sum>j\<le>k-1. ws ! j * geometric_sum k (m-j))"
    using sum_eq_ineq by fastforce
  also have "... =  1 / k *
          (\<Sum>j\<in>{nat m}.  ws ! j * geometric_sum k (m-j))"
    using sum_eq by argo
  also have "... = 1 / k * ws ! (nat m) * k"
    by(simp add: geo_k_0 assms(1) algebra_simps)
  finally have "poly (fourier_poly ws) (unity_root k m) = ws ! (nat m)"
    using assms(1) by auto
  then show ?thesis by simp
qed

lemma roots_of_unit:
  assumes "length ws > 0"
  defines "k == length ws"
  assumes "(degree p \<le> k - 1) \<and> (\<forall> m \<le> k-1. (ws ! m) = poly p (unity_root k m))"
  shows "p = fourier_poly ws"
proof -  
  let ?z = "map (\<lambda> m. unity_root k m) [0..<k]" 
  have d: "distinct ?z" using distinct_z k_def by blast
  
  let ?zs_ws = "zip ?z ws"
  from lagrange[of "?zs_ws"] have 
    "\<exists>!p. degree p \<le> k - 1 \<and>
       (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly p x = y) "
    using d assms by auto 
  from degree_fourier 
  have "degree (fourier_poly ws) \<le> k - 1"
    using k_def by simp

  from interpolate_fourier[of _ k ws]
  have "poly (fourier_poly ws) x = y"
    if "(x, y) \<in> set ?zs_ws" for x y
    
qed
  

end