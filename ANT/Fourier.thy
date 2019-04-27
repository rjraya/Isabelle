theory Fourier
  imports 
    "HOL-Number_Theory.Number_Theory"
    "HOL-Analysis.Analysis"
    Dirichlet_Series.Moebius_Mu
    Polynomial_Interpolation.Lagrange_Interpolation
    Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
begin

section\<open>Sums\<close>

lemma sum_eq_ineq: "n > 0 \<Longrightarrow> (\<Sum>i\<le>n-1. f i) = (\<Sum>i<n. f i)" 
  for n :: nat and f :: "nat \<Rightarrow> complex"
  by (metis Suc_diff_1 lessThan_Suc_atMost)

lemma g_sum_eq_ineq:
  "n > 0 \<Longrightarrow> (\<Sum>i\<in>{d..n-1}. f i) = (\<Sum>i\<in>{d..<n}. f i)" 
  for n :: nat and f :: "nat \<Rightarrow> complex"
  by (metis One_nat_def Suc_pred atLeastLessThanSuc_atLeastAtMost)

lemma sum_div_reduce: (* generalize *)
  fixes d :: nat and f :: "nat \<Rightarrow> complex"
  assumes "d dvd k" 
  assumes "d > 0" 
  shows "
   (\<Sum>n | n \<in> {1..k} \<and> d dvd n. f n) =
   (\<Sum>c \<in> {1..k div d}. f (c*d))" 
   by(rule sum.reindex_bij_witness[of _ "\<lambda>k. k * d" "\<lambda>k. k div d"])
     (use assms  in \<open>fastforce simp: div_le_mono\<close>)+

section\<open>Periodic functions\<close>

definition 
  "periodic f k = (\<forall> n. f(n+k) = f(n))" 
  for n :: int and k :: nat and f :: "nat \<Rightarrow> complex"

lemma const_periodic:
  "periodic (\<lambda> x. y) 0" 
  unfolding periodic_def by blast

lemma add_periodic:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "periodic f k"
  assumes "periodic g k"
  shows "periodic (\<lambda> n. f n + g n) k"
  using assms unfolding periodic_def by simp

lemma mult_periodic:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "periodic f k"
  assumes "periodic g k"
  shows "periodic (\<lambda> n. f n * g n) k"
  using assms unfolding periodic_def  by simp

lemma fin_sum_periodic:
  fixes f g :: "nat \<Rightarrow> complex" and l :: nat
  assumes "\<forall> i<l. periodic (h i) k"
  shows "periodic (\<lambda> n. (\<Sum>i<l. h i n)) k"
  using assms
proof(induction l)
  case 0 then show ?case by(simp add: periodic_def)
next
  case (Suc l)
  show ?case 
  proof -    
    have "(\<Sum>i<Suc l. h i n) = (\<Sum>i<l. h i n) +  h l n"
      for n by simp
    then have "periodic (\<lambda>n. \<Sum>i<Suc l. h i n) k = 
               periodic (\<lambda>n. (\<Sum>i<l. h i n) +  h l n) k"
      by simp
    from this Suc assms add_periodic 
    show ?thesis by (simp add: periodic_def)
  qed
qed

(* this should replace the above, it is the right generalization *)
lemma fin_sum_periodic_set:
  fixes f g :: "nat \<Rightarrow> complex" 
  assumes "\<forall> i \<in> A. periodic (h i) k"
  shows "periodic (\<lambda> n. (\<Sum>i \<in> A. h i n)) k"
  using assms by(simp add: periodic_def)

lemma mult_period:
  assumes "periodic g k"
  shows "periodic g (k*q)"
  using assms
proof(induction q arbitrary: k)
  case 0
then show ?case unfolding periodic_def by simp
next
  case (Suc m)
  then show ?case 
    unfolding periodic_def
    by (simp,metis add.assoc add.commute)
qed
  
lemma unique_periodic_extension:
  assumes "k > 0"
  assumes "\<forall> j<k. g j = h j"
  assumes "periodic g k" and "periodic h k"
  shows "g i = h i"
proof(cases "i < k")
  case True then show ?thesis using assms by simp
next
  case False then show ?thesis 
  proof -
    have "(i div k)*k + (i mod k) = i \<and> (i mod k) < k" 
      by(simp add: assms(1) algebra_simps)
    then obtain q r where euclid_div: "k*q + r = i \<and> r < k"
      using mult.commute by metis
    from assms(3) assms(4) 
    have period: "periodic g (k*q) \<and> periodic h (k*q)" 
      using mult_period by simp
    then have "g(k*q+r) = g(r)" 
      unfolding periodic_def using add.commute by metis
    also have "... = h(r)" 
      using euclid_div assms(2) by simp
    also have "... = h(k*q+r)"
      using period add.commute unfolding periodic_def by metis
    also have "... = h(i)" using euclid_div by simp
    finally show "g(i) = h(i)" using euclid_div by simp
  qed
qed
                  
lemma periodic_sum_periodic:
  assumes "periodic f k"
  shows "(\<Sum>l \<in> {m..n}. f l) = (\<Sum>l \<in> {m+k..n+k}. f l)"
  using periodic_def assms 
  by(intro sum.reindex_bij_witness
         [of "{m..n}" "\<lambda> l. l-k" "\<lambda> l. l+k" "{m+k..n+k}" f f])
      auto

lemma mod_periodic:
  fixes n m :: nat
  assumes "periodic f k"
  assumes "n mod k = m mod k"
  shows "f n = f m"
proof -
  obtain q  where 1: "n = q*k+(n mod k)" 
     using div_mult_mod_eq[of n k] by metis
  obtain q' where 2: "m = q'*k+(m mod k)"
     using div_mult_mod_eq[of m k] by metis
  from 1 have "f n = f (q*k+(n mod k))" by auto
  also have "... = f (n mod k)"
    using mult_period[of f k q] assms(1) periodic_def[of f "k*q"]
    by(simp add: algebra_simps, metis add.commute) 
  also have "... = f (m mod k)" using assms(2) by auto
  also have "... = f (q'*k+(m mod k))"
    using mult_period[of f k q'] assms(1) periodic_def[of f "k*q'"]
    by(simp add: algebra_simps, metis add.commute) 
  also have "... = f m" using 2 by auto
  finally show "f n = f m" by simp
qed

lemma cong_nat_imp_eq:
  fixes m :: nat
  assumes "m > 0"
  assumes "x \<in> {a..<a+m}" "y \<in> {a..<a+m}" "[x = y] (mod m)"
  shows   "x = y"
  using assms
proof (induction x y rule: linorder_wlog)
  case (le x y)
  have "[y - x = 0] (mod m)"
    using cong_diff_iff_cong_0_nat cong_sym le by blast
  thus "x = y"
    using le by (auto simp: cong_def)
qed (auto simp: cong_sym)

lemma inj_on_mod_nat:
  fixes m :: nat
  assumes "m > 0"
  shows   "inj_on (\<lambda>x. x mod m) {a..<a+m}"
proof
  fix x y assume xy: "x \<in> {a..<a+m}" "y \<in> {a..<a+m}" and eq: "x mod m = y mod m"
  from \<open>m > 0\<close> and xy show "x = y"
    by (rule cong_nat_imp_eq) (use eq in \<open>simp_all add: cong_def\<close>)
qed

lemma bij_betw_mod_nat_atLeastLessThan:
  fixes k d :: nat
  assumes "k > 0"
  defines "g \<equiv> (\<lambda>i. nat ((int i - int d) mod int k) + d)"
  shows   "bij_betw (\<lambda>i. i mod k) {d..<d+k} {..<k}"
  unfolding bij_betw_def
proof
  show inj: "inj_on (\<lambda>i. i mod k) {d..<d + k}"
    by (rule inj_on_mod_nat) fact+
  have "(\<lambda>i. i mod k) ` {d..<d + k} \<subseteq> {..<k}"
    by auto
  moreover have "card ((\<lambda>i. i mod k) ` {d..<d + k}) = card {..<k}"
    using inj by (subst card_image) auto
  ultimately show "(\<lambda>i. i mod k) ` {d..<d + k} = {..<k}"
    by (intro card_subset_eq) auto
qed

corollary bij_betw_shift:
 fixes k d d' :: nat
 assumes "k > 0"
 shows   "\<exists> b. bij_betw b {d..<d+k} {d'..<d'+k}"
proof -
  have 1: "bij_betw (\<lambda>i. i mod k) {d..<d+k} {0..<k}"
    using bij_betw_mod_nat_atLeastLessThan[of k d] 
    by (simp add: assms(1) atLeast0LessThan)
  have "bij_betw (\<lambda>i. i mod k) {d'..<d'+k} {0..<k}"
    using bij_betw_mod_nat_atLeastLessThan[of k d']
    by (simp add: assms(1) atLeast0LessThan)
  then obtain g where 2: "bij_betw g {0..<k} {d'..<d'+k}"
    using bij_betw_inv by blast
  from 1 2 obtain h where  "bij_betw h {d..<d+k} {d'..<d'+k}"
    using bij_betw_trans by blast
  then show ?thesis by blast
qed

lemma periodic_sum_periodic_shift:
  fixes k d :: nat
  assumes "periodic f k" 
  assumes "k > 0" 
  assumes "d > 0"
  shows "(\<Sum>l \<in> {0..k-1}. f l) = 
         (\<Sum>l \<in> {d..d+k-1}. f l)"
proof -
  have "(\<Sum>l \<in> {0..k-1}. f l) = (\<Sum>l \<in> {0..<k}. f l)"
    using g_sum_eq_ineq assms(2) by blast
  also have "... = (\<Sum>l \<in> {d..<d+k}. f (l mod k))"
    using assms(2) 
    by (simp add: sum.reindex_bij_betw[OF bij_betw_mod_nat_atLeastLessThan[of k d]] 
                  lessThan_atLeast0)
  also have "... = (\<Sum>l \<in> {d..<d+k}. f l)"
    using mod_periodic[of f k] assms(1) sum.cong
    by (meson mod_mod_trivial)
  also have "... = (\<Sum>l \<in> {d..d+k-1}. f l)"
    using g_sum_eq_ineq[of "d+k" f d] assms(2-3) by fastforce
  finally show ?thesis by auto
qed

(*
lemma periodic_sum_periodic_shift:
  fixes k d d' :: nat
  assumes "periodic f k" 
  assumes "k > 0" 
  shows "(\<Sum>l \<in> {d..d+k-1}. f l) = 
         (\<Sum>l \<in> {d'..d'+k-1}. f l)"
*)

section\<open>Gcd\<close>

lemma sub:
  fixes a b c d :: nat
  assumes "coprime a c" "coprime a d" "coprime b c" "coprime b d"
  shows "coprime (a*b) (c*d)"
  by (simp add: assms)

lemma linear_gcd:
  fixes a b c d :: nat
  assumes "a > 0" "b > 0" "c > 0" "d > 0"
  assumes "coprime a c" "coprime b d" 
  shows "gcd (a*b) (c*d) = (gcd a d) * (gcd b c)"
proof -
  define q1 :: nat where "q1 = a div gcd a d" 
  define q2 :: nat where "q2 = c div gcd b c" 
  define q3 :: nat where "q3 = b div gcd b c"
  define q4 :: nat where "q4 = d div gcd a d"
  
  from this assms
  have "coprime q1 q2" "coprime q3 q4" 
    unfolding q1_def q2_def q3_def q4_def
    by (metis coprime_commute coprime_mult_left_iff 
              dvd_div_mult_self gcd_dvd1 gcd_dvd2)+
  moreover have "coprime q1 q4" "coprime q3 q2"
    unfolding q1_def q2_def q3_def q4_def 
    using assms div_gcd_coprime by blast+
  ultimately have 1: "coprime (q1*q3) (q2*q4)"
    using  sub[of q1 q2 q4 q3] by simp    
  have "gcd (a*b) (c*d) = (gcd a d) * (gcd b c) * gcd (q1*q3) (q2*q4)"
    unfolding q1_def q2_def q3_def q4_def
    using gcd_mult_distrib_nat dvd_div_mult_self gcd_dvd1 gcd_dvd2
    by (smt mult.assoc mult.commute) (* fix this *)
  from this 1 show "gcd (a*b) (c*d) = (gcd a d) * (gcd b c)" by auto
qed  

lemma reindex_product_bij:
  fixes a b m k :: nat
  defines "S \<equiv> {(d1,d2). d1 dvd gcd a m \<and> d2 dvd gcd k b}"
  defines "T \<equiv> {d. d dvd (gcd a m) * (gcd k b)}"
  defines "f \<equiv> (\<lambda> (d1,d2). d1 * d2)"
  assumes "coprime a k"
  shows "bij_betw f S T"
  unfolding bij_betw_def
proof
  show inj: "inj_on f S"
    unfolding f_def 
  proof -
    {fix d1 d2 d1' d2'
    assume "(d1,d2) \<in> S" "(d1',d2') \<in> S"
    then have dvd: "d1 dvd gcd a m" "d2 dvd gcd k b" 
              "d1' dvd gcd a m" "d2' dvd gcd k b"
      unfolding S_def by simp+
    assume "f (d1,d2) = f (d1',d2')" 
    then have eq: "d1 * d2 = d1' * d2'" 
      unfolding f_def by simp
    from eq dvd have eq1: "d1 = d1'" 
      by (simp,meson assms coprime_crossproduct_nat coprime_divisors)
    from eq dvd have eq2: "d2 = d2'"
      by (metis assms(4) coprime_commute coprime_divisors coprime_dvd_mult_right_iff  
           dvd_triv_right gcd_nat.antisym gcd_nat.boundedE)
    from eq1 eq2 have "d1 = d1' \<and> d2 = d2'" by simp} 
   then show "inj_on (\<lambda>(d1, d2). d1 * d2) S" 
    using S_def f_def by(intro inj_onI,blast)
  qed
  show surj: "f ` S = T" 
  proof -
    {fix d
      have "d dvd (gcd a m) * (gcd k b)
       \<longleftrightarrow> (\<exists> d1 d2. d = d1*d2 \<and> d1 dvd gcd a m \<and> d2 dvd gcd k b)"
        using division_decomp mult_dvd_mono by blast}
      then show ?thesis
        unfolding f_def S_def T_def image_def
        by auto
  qed
qed

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

lemma unity_minus: "unity_root k (-n) = inverse (unity_root k n)"
  unfolding unity_root_def by simp

lemma unity_periodic:
  "periodic (unity_root k) k" 
  unfolding periodic_def 
proof
  fix n
  have "unity_root k (n + k) = unity_root k ((n+k) mod k)"
    using unity_mod[of k] zmod_int by presburger
  also have "unity_root k ((n+k) mod k) = unity_root k n" 
    using unity_mod zmod_int by auto
  finally show "unity_root k (n + k) = unity_root k n" by simp
qed

lemma unity_periodic_mult:
  "periodic (\<lambda> n. unity_root k (m * int n)) k"
  unfolding periodic_def
proof 
  fix n
  have "unity_root k (m * int (n + k)) = 
        unity_root k (m*n + m*k)"
    by(simp add: algebra_simps)
  also have "... = unity_root k (m*n)"
    using mult_period unfolding periodic_def
    by (metis add.commute calculation mod_mult_self3 unity_mod unity_pow)
  finally show "unity_root k (m * int (n + k)) =
             unity_root k (m * int n)" by simp
qed

lemma unity_periodic_mult_minus:
  shows "periodic (\<lambda> i. unity_root k (-int i*int m)) k" 
  unfolding periodic_def
proof 
  fix n 
   have "unity_root k (-(n + k) * m) = 
        inverse(unity_root k ((n + k) * m))" 
     using unity_minus[of k "(n + k) * m"] 
     by (metis mult_minus_left of_nat_mult)
  also have "... = inverse(unity_root k (n*m+k*m))"
    by(simp add: algebra_simps)
  also have "... = inverse(unity_root k (n*m))"
    using mult_period[of "unity_root k" k m] unity_periodic[of k]
    unfolding periodic_def by presburger
  also have "... = unity_root k (-n*m)"
    using unity_minus[of k "n*m"] by simp
  finally show "unity_root k (-(n + k) * m) = unity_root k (-n*m)"
    by simp
qed

lemma unity_div:
 fixes a :: int and d :: nat
 assumes "d dvd k"
 shows "unity_root k (a*d) = unity_root (k div d) a" 
proof -
  have 1: "(2*pi*(a*d)/k) = (2*pi*a)/(k div d)"
    using Suc_pred assms by(simp add: divide_simps, fastforce)   
  have "unity_root k (a*d) = exp ((2*pi*(a*d)/k)* \<i>)"
    using unity_exp by simp
  also have "... = exp (((2*pi*a)/(k div d))* \<i>)"
    using 1 by simp
  also have "... = unity_root (k div d) a"
    using unity_exp by simp
  finally show ?thesis by simp
qed

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
 "periodic (geometric_sum k) k"
  unfolding periodic_def
proof 
  fix n 
  show "geometric_sum k (n + k) = geometric_sum k n"
    by(cases "k = 0", simp,
       cases "k dvd n",
       auto simp add:  gs_case_1 gs_case_2)
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

corollary lagrange:
 "length zs_ws > 0 \<Longrightarrow>
  distinct (map fst zs_ws) \<Longrightarrow>
  (\<exists>! (p :: complex poly).
    degree p \<le> (length zs_ws)-1 \<and>
    (\<forall> x y. (x,y) \<in> set zs_ws \<longrightarrow> poly p x = y))"
  using lagrange_exists lagrange_unique by blast

subsection\<open>List version\<close>

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
  then show ?thesis by Groebner_Basis.algebra
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
  fixes m :: int and ws
  defines "k == length ws"
  assumes "m \<in> {0..<k}"
  assumes "m < length ws"
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
    using assms(2) by(intro sum.mono_neutral_right,auto)

  have "poly (fourier_poly ws) (unity_root k m) = 
        (\<Sum>i\<le>k-1. coeff (fourier_poly ws) i * (unity_root k m) ^ i)"
    using degree_fourier[of ws] k_def
          extended_altdef[of "fourier_poly ws" "k-1" 
                             "unity_root k m"]
    by blast
  also have "... = (\<Sum>i<k. coeff (fourier_poly ws) i * (unity_root k m) ^ i)"
    using sum_eq_ineq assms(2) by auto
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
    by (metis (no_types, lifting) divide_eq_0_iff gr0I mult_cancel_left of_nat_0 of_real_eq_0_iff)
  also have "... = 1 / k * (\<Sum>j<k. ws ! j * geometric_sum k (m-j))"
    using geometric_sum_def 
    by(simp add: algebra_simps)
  also have "... = 1 / k * (\<Sum>j\<le>k-1. ws ! j * geometric_sum k (m-j))"
    using sum_eq_ineq by fastforce
  also have "... =  1 / k *
          (\<Sum>j\<in>{nat m}.  ws ! j * geometric_sum k (m-j))"
    using sum_eq by argo
  also have "... = 1 / k * ws ! (nat m) * k"
    using geo_k_0 assms(2) by(auto simp add: algebra_simps)
  finally have "poly (fourier_poly ws) (unity_root k m) = ws ! (nat m)"
    using assms(2) by auto
  then show ?thesis by simp
qed

(* theorem 8.3 *)
lemma fourier_expansion_unique:
  assumes "length ws > 0"
  defines "k == length ws"
  assumes "(degree p \<le> k - 1)"
  assumes "(\<forall> m \<le> k-1. (ws ! m) = poly p (unity_root k m))"
  shows "p = fourier_poly ws"
proof -  
  let ?z = "map (\<lambda> m. unity_root k m) [0..<k]" 
  have d1: "distinct ?z" using distinct_z k_def by blast
  
  let ?zs_ws = "zip ?z ws"
  from d1 k_def have d2: "distinct (map fst ?zs_ws)" by simp
  have l2: "length ?zs_ws > 0" using assms(1) k_def by auto
  have l3: "length ?zs_ws = k" by (simp add: k_def)

  from degree_fourier
  have degree: "degree (fourier_poly ws) \<le> k - 1"
    using k_def by simp

  have interp: "poly (fourier_poly ws) x = y"
    if "(x, y) \<in> set ?zs_ws" for x y
  proof -
    from that obtain n where "
         x = map (unity_root k \<circ> int) [0..<k] ! n \<and>
         y = ws ! n \<and> 
         n < length ws"
      using in_set_zip[of "(x,y)" "(map (unity_root k) (map int [0..<k]))" ws]
      by auto
    then have "
         x = unity_root k (int n) \<and>
         y = ws ! n \<and> 
         n < length ws"
      using nth_map[of n "[0..<k]" "unity_root k \<circ> int" ] k_def by simp
    from this interpolate_fourier[of n ws] k_def
    show "poly (fourier_poly ws) x = y" by simp          
  qed

  have interp_p: 
   "poly p x = y"
   if "(x,y) \<in> set ?zs_ws" for x y
  proof -
    from that obtain n where "
         x = map (unity_root k \<circ> int) [0..<k] ! n \<and>
         y = ws ! n \<and> 
         n < length ws"
      using in_set_zip[of "(x,y)" "(map (unity_root k) (map int [0..<k]))" ws]
      by auto
    then have "
         x = unity_root k (int n) \<and>
         y = ws ! n \<and> 
         n < length ws"
      using nth_map[of n "[0..<k]" "unity_root k \<circ> int" ] k_def by simp
    from this assms(4) k_def
    show "poly p x = y" 
      by (metis One_nat_def Suc_pred assms(1) not_le not_less_eq_eq)       
  qed

  from lagrange_unique[of _ p "fourier_poly ws"] d2 l2
  have l: "
    degree p \<le> k - 1 \<and>
    (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly p x = y) \<Longrightarrow>
    degree (fourier_poly ws) \<le> k - 1 \<and>
    (\<forall>x y. (x, y) \<in> set ?zs_ws \<longrightarrow> poly (fourier_poly ws) x = y) \<Longrightarrow>
    p = (fourier_poly ws)"
    using l3 by fastforce
  from assms degree interp interp_p l3
  show "p = (fourier_poly ws)" using l by blast  
qed

lemma 
 "periodic (poly (fourier_poly ws)) (length ws)"
  oops

subsection\<open>Functional version\<close>

(* use lift_definition *)

definition fourier_fun :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex poly" where
"fourier_fun ws k =
  (poly_of_list [1 / k * (\<Sum>m<k. (ws m) 
    * unity_root k (-n*m)). n \<leftarrow> [0..<k]])"

lemma fourier_fun_list:
  shows "fourier_poly [ws n. n \<leftarrow> [0..<k]] = 
         fourier_fun ws k"
  unfolding fourier_fun_def fourier_poly_def by simp

lemma coeff_fun: 
  assumes "n < k"
  shows "coeff (fourier_fun ws k) n = 
         (1/k) * (\<Sum>m < k. (ws m) * unity_root k (-n*m))"
proof -
  let ?ws = "[ws n. n \<leftarrow> [0..<k]]"
  have "coeff (fourier_fun ws k) n =
        coeff (fourier_poly ?ws) n" 
    using fourier_fun_list by simp
  also have "coeff (fourier_poly ?ws) n = 
    1 / k * (\<Sum>m<k. (?ws ! m) * unity_root k (- n*m))" 
    using coeff_fourier assms by auto
  also have "... = (1/k) * (\<Sum>m < k. (ws m) * unity_root k (-n*m))"
    using assms by simp
  finally show ?thesis by simp    
qed

lemma degree_fun: "degree (fourier_fun ws k) \<le> k - 1"
  using degree_fourier fourier_fun_list
  by (metis diff_zero length_map length_upt)

lemma interpolate_fun:
  fixes m :: int and k
  assumes "m \<in> {0..<k}"
  shows "poly (fourier_fun ws k) (unity_root k m) = (ws (nat m))"
proof -
  let ?ws = "[ws n. n \<leftarrow> [0..<k]]"
  have "poly (fourier_fun ws k) (unity_root k m) = 
        poly (fourier_poly ?ws) (unity_root k m)" 
    using fourier_fun_list by simp
  also have "... = (?ws ! (nat m))"
    using interpolate_fourier assms
    by (metis atLeastLessThan_iff diff_zero length_map length_upt)
  also have "... = (ws (nat m))"
    using assms by auto
  finally show "poly (fourier_fun ws k) (unity_root k m) = (ws (nat m))"
    by simp
qed

lemma fun_expansion_unique:
  assumes "k > 0"
  assumes "(degree p \<le> k - 1)"
  assumes "(\<forall> m \<le> k-1. (ws  m) = poly p (unity_root k m))"
  shows "p = fourier_fun ws k"
proof -
  let ?ws = "[ws n. n \<leftarrow> [0..<k]]"
  from fourier_expansion_unique 
  have "p = fourier_poly ?ws" using assms by simp
  also have "... = fourier_fun ws k"
    using fourier_fun_list by blast
  finally show "p = fourier_fun ws k" by blast
qed

lemma on_units:
  fixes k :: nat
  assumes "k > 0" 
  shows "poly (fourier_fun f k) (unity_root k m) = 
    (\<Sum>n<k.1/k*(\<Sum>m<k.(f m)*unity_root k (-n*m))*unity_root k (m*n))"
proof -
  have "poly (fourier_fun f k) (unity_root k m) = 
        (\<Sum>n\<le>k-1. coeff (fourier_fun f k) n *(unity_root k m)^n)"
    using extended_altdef[of "fourier_fun f k" "k-1" "unity_root k m"]
          degree_fun[of f k] by simp
  also have "... = (\<Sum>n\<le>k-1. coeff (fourier_fun f k) n *(unity_root k (m*n)))" 
    using unity_pow by simp
  also have "... = (\<Sum>n<k. coeff (fourier_fun f k) n *(unity_root k (m*n)))" 
    using sum_eq_ineq assms by simp
  also have "... = (\<Sum>n<k.(1/k)*(\<Sum>m<k.(f m)*unity_root k (-n*m))*(unity_root k (m*n)))" 
    using coeff_fun[of _ k f] by simp
  finally show
   "poly (fourier_fun f k) (unity_root k m) = 
    (\<Sum>n<k.1/k*(\<Sum>m<k.(f m)*unity_root k (-n*m))*unity_root k (m*n))"
    by blast
qed
  
subsection\<open>Finite Fourier expansion of an arithmetical function\<close>

lemma fourier_expansion:
  assumes "k > 0"
  assumes "periodic f k"
  assumes "g = (\<lambda> n. (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m)))"
  shows "periodic g k" and
        "f(m) = (\<Sum>n<k. g(n)* unity_root k (m*n))"  
proof -
  show 1: "periodic g k"
    unfolding periodic_def
  proof 
    fix n
    from unity_periodic mult_period
    have period: "periodic (\<lambda>x. unity_root k x) (k*m)" by simp

    have "unity_root k (-(n+k)*m) = unity_root k (-n*m-k*m)"
      by(simp add: field_simps,
         metis ab_group_add_class.ab_diff_conv_add_uminus add.commute)
    also have "unity_root k (-n*m-k*m) = unity_root k (-n*m)"
      using period unity_minus unfolding periodic_def 
      by (metis calculation distrib_right mult_minus_left of_nat_mult)
    finally have u_period: "unity_root k (-(n+k)*m) = unity_root k (-n*m)" by simp

    have "g(n+k) = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-(n+k)*m))"
      using assms(3) by fastforce
    also have "... = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"
      using u_period 
      by (metis (no_types, hide_lams) mod_add_self2 unity_minus unity_mod unity_pow zmod_int)
    also have "... = g(n)"
      using assms(3) by fastforce
    finally show "g(n+k) = g(n)" by simp 
  qed

  show "f(m) = (\<Sum>n<k. g(n)* unity_root k (m * int n))"
  proof -
    { 
      fix m
      assume range: "m \<in> {0..<k}"
      have "f(m) = (\<Sum>n<k. g(n)* unity_root k (m * int n))"
      proof -
        from interpolate_fun[of _ k f] 
        have "f m = poly (fourier_fun f k) (unity_root k m)"
          using range by simp
        also have "... = (\<Sum>n<k. (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))* unity_root k (m*n))"
          using on_units assms(1) by blast
        also have "... = (\<Sum>n<k. g(n)* unity_root k (m*n))"
          using assms by simp
        finally show ?thesis by auto
    qed}
  note concentrated = this

  have "periodic (\<lambda> m. (\<Sum>n<k. g(n)* unity_root k (m * int n))) k"
  proof - 
    have "periodic (\<lambda> n. g(n)* unity_root k (i * int n)) k"  for i :: int
     using 1 unity_periodic mult_periodic unity_periodic_mult by auto
     then have "\<forall>i<k. periodic (\<lambda> n. g(n)* unity_root k (i * int n)) k"
      by simp
    then have "periodic (\<lambda>i. \<Sum>n<k. g(n)* unity_root k (i * int n)) k"
      using fin_sum_periodic[of k _ k] (* fix this *)
      by (smt mod_add_self2 periodic_def sum.cong unity_mod unity_pow zmod_int)        
   then show ?thesis by simp
 qed  
  
 from  this assms(1-2) concentrated 
       unique_periodic_extension[of k f "(\<lambda>i. \<Sum>n<k. g(n)* unity_root k (i * int n))"  m]
  show "f m = (\<Sum>n<k. g n * unity_root k (int m * int n))" by simp        
  qed
qed

lemma fourier_uniqueness:
  fixes f g :: "nat \<Rightarrow> complex" 
  assumes "k > 0"
  assumes "periodic f k" and "periodic g k" (*periodicity of g required by theorem? *)
  assumes "\<And> m. f(m) = (\<Sum>n<k. g(n)* unity_root k (int (m*n)))" 
  shows "g(n) = ((1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m)))"
proof -
  let ?p = "poly_of_list [g(n). n \<leftarrow> [0..<k]]"
  have d: "degree ?p \<le> k-1" 
    by (metis degree_poly diff_zero length_map length_upt)
  have c: "coeff ?p i = (if i < k then g(i) else 0)" for i
    by (simp add: nth_default_def)
  {fix z
  have "poly ?p z = (\<Sum>n\<le>k-1. coeff ?p n* z^n)" 
    using extended_altdef[of ?p "k-1"] d by blast
  then have "poly ?p z = (\<Sum>n<k. coeff ?p n* z^n)" 
    using sum_eq_ineq by (simp add: assms(1))
  then have "poly ?p z = (\<Sum>n<k. (if n < k then g(n) else 0)* z^n)"
    using c by simp
  then have "poly ?p z = (\<Sum>n<k. g(n)* z^n)" 
    by(simp split: if_splits)}
  note eval = this
  {fix i
  have "poly ?p (unity_root k i) = (\<Sum>n<k. g(n)* (unity_root k i)^n)"
    using eval by blast
  then have "poly ?p (unity_root k i) = (\<Sum>n<k. g(n)* (unity_root k (i*n)))"
    using unity_pow by auto}
  note interpolation = this

  {fix m 
  assume b: "m \<le> k-1"
  from d assms(1)
  have "f m =  (\<Sum>n<k. g(n) * unity_root k (m*n))" 
    using assms(4) by blast 
  also have "... = poly ?p (unity_root k m)"
    using interpolation by simp
  finally have "f m = poly ?p (unity_root k m)" by auto}

  from this fun_expansion_unique[of k _ f]
  have p_is_fourier: "?p = fourier_fun f k"
    using assms(1) d by blast

  {fix n 
  assume b: "n \<le> k-1"
  have "coeff ?p n = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"  
    using p_is_fourier coeff_fun using assms(1) b by auto
  then have "g(n) = (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))"
    using c b assms(1) 
    by (metis One_nat_def Suc_pred diff_le_self le_neq_implies_less le_trans less_Suc_eq_le nat_less_le poly_of_list_def)
  }
 (* now show right hand side is periodic and use unique_periodic_extension *)
  have "periodic (\<lambda> n. (1 / k) * (\<Sum>m<k. f(m) * unity_root k (-n*m))) k"
  proof - 
    have "periodic (\<lambda> i. unity_root k (-int i*int m)) k" for m
      using unity_periodic_mult_minus by simp
    then have "periodic (\<lambda> i. f(m) * unity_root k (-i*m)) k" for m
      by (simp add: periodic_def)
    then show "periodic (\<lambda>i. (1 / k) *(\<Sum>m<k. f m * unity_root k (-i*m))) k"
      using fin_sum_periodic[of k 
               "(\<lambda> m i. f m * unity_root k (-i*m))" k] periodic_def by auto
  qed
  note periodich = this
  let ?h = "(\<lambda>i. (1 / k) *(\<Sum>m<k. f m * unity_root k (-i*m)))"
  from unique_periodic_extension[of k g ?h n] 
        assms(3) assms(1) periodich
  have "g n = (1/k) * (\<Sum>m<k. f m * unity_root k (-n*m))" 
    by (simp add: \<open>\<And>na. na \<le> k - 1 \<Longrightarrow> g na = complex_of_real (1 / real k) * (\<Sum>m<k. f m * unity_root k (- int na * int m))\<close>)
  then show ?thesis by simp
qed  
        
section\<open>Ramanujan's sums\<close>

subsection\<open>Dirichlet product neutral element\<close>

definition "I n = (if n = 1 then 1 else 0)" for n :: nat

lemma I_intro: 
  fixes S :: "nat \<Rightarrow> complex" and f :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  defines "S \<equiv> (\<lambda> (n::nat). (\<Sum> k | k \<in> {1..n} \<and> coprime k n. (f k n)))" 
  shows "S(n) = (\<Sum> k \<in> {1..n}. (f k n)* (I (gcd k n)))"
proof -
  let ?g = "\<lambda> k. (f k n)* (I (gcd k n))"
  have zeros: "\<forall> k \<in> {1..n} - {k. k \<in> {1..n} \<and> coprime k n}. ?g k = 0"
  proof
    fix k 
    assume "k \<in> {1..n} - {k \<in> {1..n}. coprime k n}"
    then show "(f k n) * I (gcd k n) = 0" 
      by(simp add: I_def[of "gcd k n"] split: if_splits,presburger) 
  qed
  
  have "S n = (\<Sum> k | k \<in> {1..n} \<and> coprime k n. (f k n))"
    by(simp add: S_def)
  also have "... = sum ?g {k. k \<in> {1..n} \<and> coprime k n}"
    by(simp add: I_def split: if_splits)    
  also have "... = sum ?g {1..n}"
    by(intro sum.mono_neutral_left, auto simp add: zeros)
  finally show ?thesis by blast 
qed

lemma I_right_neutral:
 "dirichlet_prod f I n = f n " if "n > 0" for f :: "nat \<Rightarrow> complex" and n 
proof -
  {fix d :: nat
    assume "d dvd n"
    then have eq: "n = d \<longleftrightarrow> n div d = 1"
      using div_self that dvd_mult_div_cancel by force
    have "f(d)*I(n div d) = (if n = d then f(d) else 0)" 
      by(simp add: I_def eq)}
  note summand = this

  have "dirichlet_prod f I n = (\<Sum> d | d dvd n. f(d)*I(n div d))"
    unfolding dirichlet_prod_def by blast
  also have "... = (\<Sum> d | d dvd n. (if n = d then f(d) else 0))"
    using summand by simp
  also have "... = (\<Sum> d | d = n. (if n = d then f(d) else 0))"
    using that by(intro sum.mono_neutral_right, auto)
  also have "... = f(n)"  by simp
  finally show ?thesis by simp 
qed

lemma I_left_neutral:
 "dirichlet_prod I f n = f n " if "n > 0" for f :: "nat \<Rightarrow> complex" and n
  using I_right_neutral dirichlet_prod_commutes that by metis

corollary I_right_neutral_0:
  fixes f :: "nat \<Rightarrow> complex" 
  assumes "f 0 = 0"
  shows "dirichlet_prod f I n = f n"
  using assms I_right_neutral by(cases n, simp, blast)

lemma I_sum: "I n = (\<Sum>k = 1..n. unity_root n k)" for n :: nat
proof(cases "n = 0")
  case True then show ?thesis unfolding I_def by simp
next
  case False
  have 1: "unity_root n 0 = 1" by (simp add: unity_k_0)
  then have 2: "unity_root n n = 1" 
    using unity_periodic[of n]
    unfolding periodic_def 
    by (metis add.left_neutral of_nat_0)
  have "(\<Sum>k = 1..n. unity_root n k) = 
        (\<Sum>k = 0..n. unity_root n k) - 1"
    by (simp add: sum_head_Suc sum.atLeast0_atMost_Suc_shift 1)
  also have "... = ((\<Sum>k = 0..n-1. unity_root n k)+1) - 1"
    using sum.atLeast0_atMost_Suc False 
    by (metis (no_types, lifting) One_nat_def Suc_pred neq0_conv 2)
  also have "... = (\<Sum>k = 0..n-1. unity_root n k)" by auto
  also have "... = geometric_sum n 1" 
    using geometric_sum_def[of n 1]
    by (simp add: atMost_atLeast0)
  also have "... = I n"
    using geometric_sum[of n 1] False
    by(cases "n = 1",auto simp add: False I_def)
  finally have 3: "I n = (\<Sum>k = 1..n. unity_root n k)" by auto
  then show ?thesis by blast 
qed

subsection\<open>Basic Ramanujan's sums\<close>

definition 
 "ramanujan k n = (\<Sum>m | m \<in> {1..k} \<and> coprime m k. unity_root k (m*n))"
 for k n :: nat

abbreviation "c k n \<equiv> ramanujan k n"

lemma c_0_n: "c 0 n = 0"
  unfolding ramanujan_def 
  using unity_0_n by simp

lemma dirichlet_coprime_sum:
  fixes F S :: "nat \<Rightarrow> complex" and f :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  defines "F \<equiv> (\<lambda> n. (\<Sum> k \<in> {1..n}. (f k n)))"
  defines "S \<equiv> (\<lambda> n. (\<Sum> k | k \<in> {1..n} \<and> coprime k n . (f k n)))"
  assumes "\<And> a b d. d dvd a \<Longrightarrow> d dvd b \<Longrightarrow> f (a div d) (b div d) = f a b" 
  shows "S n = dirichlet_prod moebius_mu F n"
proof(cases "n = 0")
  case True
  then show ?thesis 
    using assms(2) unfolding dirichlet_prod_def  by fastforce
next
  case False
  have "S(n) = (\<Sum> k | k \<in> {1..n} \<and> coprime k n . (f k n))"
    using assms by blast
  also have "... = (\<Sum> k \<in> {1..n}. (f k n)* I (gcd k n))"
    using I_intro by blast
  also have "... = (\<Sum> k \<in> {1..n}. (f k n)* (\<Sum>d | d dvd (gcd k n). moebius_mu d))"
  proof -
    {fix k
    have "I (gcd k n) = (if gcd k n = 1 then 1 else 0)"
      using I_def[of "gcd k n"] by blast
    also have "... = (\<Sum>d | d dvd gcd k n. moebius_mu d)"
      using sum_moebius_mu_divisors'[of "gcd k n"] by auto
    finally have "I (gcd k n) = (\<Sum>d | d dvd gcd k n. moebius_mu d)" 
      by auto
    } note summand = this
    then show ?thesis by (simp add: summand)
  qed
  also have "... = (\<Sum>k = 1..n. (\<Sum>d | d dvd gcd k n. (f k n) *  moebius_mu d))"
    by(simp add: sum_distrib_left)
  also have "... = (\<Sum>k = 1..n. (\<Sum>d | d dvd gcd n k. (f k n) *  moebius_mu d))"
    using gcd.commute[of _ n] by simp
  also have "... = (\<Sum>d | d dvd n. \<Sum>k | k \<in> {1..n} \<and> d dvd k. (f k n) * moebius_mu d)"
    using sum.swap_restrict[of "{1..n}" "{d. d dvd n}"
             "\<lambda> k d. (f k n)*moebius_mu d" "\<lambda> k d. d dvd k"] False by auto
  also have "... = (\<Sum>d | d dvd n. moebius_mu d * (\<Sum>k | k \<in> {1..n} \<and> d dvd k. (f k n)))" 
    by (simp add: sum_distrib_left mult.commute)
  also have "... = (\<Sum>d | d dvd n. moebius_mu d * (\<Sum>q \<in> {1..n div d}. (f q (n div d))))"
  proof - 
    have "
      (\<Sum>k | k \<in> {1..n} \<and> d dvd k. (f k n)) =
        (\<Sum>q \<in> {1..n div d}. (f q (n div d)))" 
      if "d dvd n" "d > 0" for d :: nat
      by(rule sum.reindex_bij_witness[of _ "\<lambda>k. k * d" "\<lambda>k. k div d"])
         (use assms(3) that in \<open>fastforce simp: div_le_mono\<close>)+
    then show ?thesis 
      by (smt False dvd_div_mult_self mem_Collect_eq mult_cancel_left mult_eq_0_iff mult_is_0 not_gr0 sum.cong)
      (* fix this: proving summation with summands should be easy with substitutions *)
  qed
  also have "... = (\<Sum>d | d dvd n. moebius_mu d * F(n div d))"
  proof - 
    have "F(n div d) = (\<Sum>q \<in> {1..n div d}. (f q (n div d)))" 
      if "d dvd n" for d
        by (simp add: F_def real_of_nat_div that)
     then show ?thesis by auto
  qed
  also have "... = dirichlet_prod moebius_mu F n"
    by(simp add: dirichlet_prod_def)
  finally show ?thesis by simp
qed

lemma moebius_coprime_sum:
  "moebius_mu n = (\<Sum> k | k \<in> {1..n} \<and> coprime k n . unity_root n k)"
  for n :: nat
proof -
  let ?f = "(\<lambda> k n. unity_root n k)"
  from div_dvd_div have " 
      d dvd a \<Longrightarrow> d dvd b \<Longrightarrow>
      unity_root (a div d) (b div d) = 
      unity_root a b" for a b d :: nat
    using unity_root_def 
    using real_of_nat_div by fastforce
  then have "(\<Sum>k | k \<in> {1..n} \<and> coprime k n. ?f k n) =
        dirichlet_prod moebius_mu (\<lambda>n. \<Sum>k = 1..n. ?f k n) n"
    using dirichlet_coprime_sum[of ?f n  ] by blast
  also have "... = dirichlet_prod moebius_mu I n"
    by(simp add: I_sum)
  also have "... = moebius_mu n" 
    by(simp add: I_right_neutral_0)
  finally have "moebius_mu n = (\<Sum>k | k \<in> {1..n} \<and> coprime k n. ?f k n)"
    by argo
  then show ?thesis by blast
qed

corollary c_k_1: "c k 1 = moebius_mu k" for k :: nat
  unfolding ramanujan_def 
  using moebius_coprime_sum[of k] by simp

lemma c_k_dvd_n:
  assumes "k dvd n"
  shows "c k n = totient k"
  unfolding ramanujan_def
proof - 
  {fix m 
  have "k dvd (m*n)" using assms by auto
  then have "unity_root k (m*n) = 1"
    using unity_0_n unity_dvd
    by(cases "k = 0", blast+)}
  then have "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. unity_root k (m * n)) = 
       (\<Sum>m | m \<in> {1..k} \<and> coprime m k. 1)" by simp
  also have "... = card {m. m \<in> {1..k} \<and> coprime m k}" by simp
  also have "... = totient k"
   unfolding totient_def totatives_def 
  proof -
    have "{1..k} = {0<..k}" by auto
    then show " of_nat (card {m \<in> {1..k}. coprime m k}) =
              of_nat (card {ka \<in> {0<..k}. coprime ka k})" by auto
  qed
  finally show "(\<Sum>m | m \<in> {1..k} \<and> coprime m k. unity_root k (m * n)) = totient k" 
    by auto
qed

definition "s f g = 
  (\<lambda> (k::nat) (n::nat). \<Sum> d | d dvd (gcd n k). f(d) * g(k div d))"
  for s :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex"

lemma s_k_1: "s f g k 1 = f(1) * g(k)"
  unfolding s_def by auto

lemma s_1_n: "s f g 1 n = f(1) * g(1)"
  unfolding s_def by simp

lemma s_k_periodic: "periodic (s f g k) k"
  unfolding s_def periodic_def by simp

theorem s_k_fourier_expansion:
  fixes f g :: "nat \<Rightarrow> complex" and a :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  assumes "k > 0" 
  defines "a \<equiv> (\<lambda> k m. (1/k) * (\<Sum>d| d dvd (gcd m k). g(d) * f(k div d) * d ))"
  shows "s f g k n = (\<Sum>m\<le>k-1. (a k m) * unity_root k (m*n))"
proof -
  let ?g = "
   (\<lambda>x. 1 / of_nat k * (\<Sum>m<k. s f g k m * unity_root k (-x*m)))"
  {fix m :: nat
  let ?h = "\<lambda> n d. f d * g (k div d) * unity_root k (- m * int n)"
  have "?g m = 1 / k * (\<Sum>l<k. s f g k l * unity_root k (-m*l))"
    by auto
  also have "... = 1 / k * (\<Sum>l \<in> {0..k-1}. s f g k l * unity_root k (-m*l))"
    using sum_eq_ineq by (simp add: assms(1) atLeast0AtMost)
  also have "... = 1 / k * (\<Sum>l \<in> {1..k}. s f g k l * unity_root k (-m*l))"
  proof -
    have "periodic (\<lambda> l. unity_root k (-m*l)) k"
      using unity_periodic_mult by blast
    then have "periodic (\<lambda> l. s f g k l * unity_root k (-m*l)) k"
      using s_k_periodic mult_periodic by blast
    from this periodic_sum_periodic_shift[of _ k 1  ]
    have "sum (\<lambda> l. s f g k l * unity_root k (-m*l)) {0..k - 1} = 
          sum (\<lambda> l. s f g k l * unity_root k (-m*l)) {1..k}"
      using assms(1) zero_less_one by simp
    then show ?thesis by argo
  qed
  also have "... = 1 / k * (\<Sum>n\<in>{1..k}. (\<Sum> d | d dvd (gcd n k). f(d) * g(k div d)) * unity_root k (-m*n))"
    by (simp add: s_def)
  also have "... = 1 / k * (\<Sum>n\<in>{1..k}. (\<Sum> d | d dvd (gcd n k). f(d) * g(k div d) * unity_root k (-m*n)))"
    by (simp add: sum_distrib_right)
  also have "... = 1 / k * (\<Sum>d | d dvd k. \<Sum>n | n \<in> {1..k} \<and> d dvd n. ?h n d)"
  proof -
    have "(\<Sum>n = 1..k. \<Sum>d | d dvd gcd n k. ?h n d) =
          (\<Sum>n = 1..k. \<Sum>d | d dvd k \<and> d dvd n . ?h n d)"
      using gcd.commute[of _ k] by simp
    also have "... = (\<Sum>d | d dvd k. \<Sum>n | n \<in> {1..k} \<and> d dvd n. ?h n d)"
      using sum.swap_restrict[of "{1..k}" "{d. d dvd k}"
                            _ "\<lambda> n d. d dvd n"] assms by fastforce
    finally have "
      (\<Sum>n = 1..k. \<Sum>d | d dvd gcd n k. ?h n d) = 
      (\<Sum>d | d dvd k. \<Sum>n | n \<in> {1..k} \<and> d dvd n. ?h n d)" by blast
    then show ?thesis by simp
  qed
  also have "... = 1 / k * (\<Sum>d | d dvd k. f(d)*g(k div d)*
             (\<Sum>n | n \<in> {1..k} \<and> d dvd n. unity_root k (- m * int n)))"
    by(simp add: sum_distrib_left)
  also have "... = 1 / k * (\<Sum>d | d dvd k. f(d)*g(k div d)*
             (\<Sum>c \<in> {1..k div d}. unity_root k (- m * (c*d))))"
    using assms(1) sum_div_reduce div_greater_zero_iff dvd_div_gt0 by auto
  also have "... = 1 / k * (\<Sum>d | d dvd k. f(d)*g(k div d)*
             (\<Sum>c \<in> {1..k div d}. unity_root (k div d) (- m * c)))"
  proof -
    {fix d c
    assume "d dvd k"
    have "unity_root k (- m * (c * d)) = 
          unity_root (k div d) (- m * c)"
      using unity_div[of d k] 
      apply(simp add: algebra_simps)
      by (metis (no_types, lifting) \<open>d dvd k\<close> mult.assoc mult.commute unity_minus)}
   then show ?thesis by simp
  qed
  also have "... = 1 / k *
                   dirichlet_prod (\<lambda> d. f(d)*g(k div d))
                   (\<lambda> d. (\<Sum>c \<in> {1..d}. unity_root d (- m *c)))
                   k"
    unfolding dirichlet_prod_def by blast
  also have "... = 1 / k *
              dirichlet_prod 
              (\<lambda> d. (\<Sum>c \<in> {1..d}. unity_root d (- m *c)))      
              (\<lambda> d. f(d)*g(k div d))       
              k"
    using dirichlet_prod_commutes[of 
            "(\<lambda> d. f(d)*g(k div d))"
            "(\<lambda> d. (\<Sum>c \<in> {1..d}. unity_root d (- m *c)))"] by argo
  also have "... = 1 / k * (\<Sum>d | d dvd k.
             (\<Sum>c \<in> {1..(d::nat)}. unity_root d (- m * c))*(f(k div d)*g(k div (k div d))))"  
    unfolding dirichlet_prod_def by blast 
  also have "... = 1 / k * (\<Sum>d | d dvd k.
             (\<Sum>c \<in> {1..(d::nat)}. unity_root d (- m * c))*(f(k div d)*g(d)))"  
  proof -
    {fix d :: nat
    assume "d dvd k"
    then have "k div (k div d) = d"
      by (simp add: assms(1) div_div_eq_right)}
    then show ?thesis by simp
  qed
  also have "... = 1 / k * (\<Sum>(d::nat) | d dvd k \<and> d dvd m.
             d*(f(k div d)*g(d)))"  
  proof -
    {fix d
    assume "d dvd k"
    have "periodic (\<lambda>x. unity_root d (- m * int x)) d"
      using unity_periodic_mult by blast
    then have "(\<Sum>c \<in> {1..d}. unity_root d (- m * c)) = 
          (\<Sum>c \<in> {0..d-1}. unity_root d (- m * c)) "
      using periodic_sum_periodic_shift[of 
          "\<lambda> c. unity_root d (- m * c)"  d 1] assms \<open>d dvd k\<close>
      by fastforce
    also have "... = geometric_sum d (-m)" 
      using geometric_sum_def 
      by (simp add: atMost_atLeast0) 
    finally have 
      "(\<Sum>c \<in> {1..d}. unity_root d (- m * c)) = geometric_sum d (-m)"
      by argo}
    then have "
      (\<Sum>d | d dvd k. (\<Sum>c = 1..d. unity_root d (- m * int c)) * 
       (f (k div d) * g d)) = 
      (\<Sum>d | d dvd k. geometric_sum d (-m) * (f (k div d) * g d))" by simp
    also have "... = (\<Sum>d | d dvd k \<and> d dvd m. geometric_sum d (-m) * (f (k div d) * g d))"
      apply(intro 
          sum.mono_neutral_right[of "{d. d dvd k}"
            "{d. d dvd k \<and> d dvd m}"
            "\<lambda> d. geometric_sum d (-m) * (f (k div d) * g d)"])
        (* fix this *)
      using geometric_sum[of _ "(-m)"] assms
      by (simp, blast, simp, 
        metis (mono_tags, lifting) DiffE assms(1) div_greater_zero_iff dvd_div_gt0 less_eq_Suc_le mem_Collect_eq)
    also have "... = (\<Sum>d | d dvd k \<and> d dvd m. d * (f (k div d) * g d))"
    proof - 
      {fix d :: nat
        assume 1: "d dvd m" 
        assume 2: "d dvd k"
        then have "geometric_sum d (-m) = d"
          using geometric_sum[of d "(-m)"] assms(1) 1 2
          by auto}
      then show ?thesis by auto
    qed
    finally show ?thesis by argo
  qed
  also have "... = (1/k) * (\<Sum>d | d dvd gcd m k.
        of_nat d * (f (k div d) * g d))" 
    by(simp add: gcd.commute)
  also have "... = (1/k) * (\<Sum>d | d dvd gcd m k.
        g d * f (k div d) * d)" 
    by(simp add: algebra_simps sum_distrib_left)
  also have "... = a k m" using a_def by auto
  finally have "?g m = a k m" by blast}
  note a_eq_g = this
  {fix m
  from fourier_expansion(2)[of k "s f g k" ] s_k_periodic assms(1) 
  have "s f g k m = (\<Sum>n<k. ?g n * unity_root k (int m * n))"
    by blast
  also have "... = (\<Sum>n<k. a k n * unity_root k (int m * n))"
    using a_eq_g by simp
  also have "... = (\<Sum>n\<le>k-1. a k n * unity_root k (int m * n))"
    using sum_eq_ineq assms(1) by simp
  finally have "s f g k m =
    (\<Sum>n\<le>k - 1. a k n * unity_root k (int n * int m))"
    by(simp add: algebra_simps)}
  then show ?thesis by blast
qed

theorem c_k_dirichlet_form:
  fixes k n :: nat
  assumes "k > 0"
  shows "c k n = (\<Sum> d | d dvd gcd n k. d * moebius_mu (k div d))"
proof -
  define a :: "nat \<Rightarrow> nat \<Rightarrow> complex" 
    where "a  =  (\<lambda> k m.
   1 / of_nat k * (\<Sum>d | d dvd gcd m k. moebius_mu d * of_nat (k div d) * of_nat d))"

  {fix m
  have "a k m = (if gcd m k = 1 then 1 else 0)"
  proof -
   have "a k m = 1 / of_nat k * (\<Sum>d | d dvd gcd m k. moebius_mu d * of_nat (k div d) * of_nat d)"
      unfolding a_def by blast
   also have 2: "... = 1 / of_nat k * (\<Sum>d | d dvd gcd m k. moebius_mu d * of_nat k)"
   proof -
     {fix d :: nat
     assume dvd: "d dvd gcd m k"
     have "moebius_mu d * of_nat (k div d) * of_nat d = moebius_mu d * of_nat k"
     proof -
       have "(k div d) * d = k" 
         using dvd by auto
       then show "moebius_mu d * of_nat (k div d) * of_nat d = moebius_mu d * of_nat k"  
         by(simp add: algebra_simps,metis of_nat_mult)
     qed} note eq = this
     show ?thesis using sum.cong by (simp add: eq)
   qed

   also have 3: "... = (\<Sum>d | d dvd gcd m k. moebius_mu d)"
     by(simp add: sum_distrib_left assms) 
   also have 4: "... =  (if gcd m k = 1 then 1 else 0)"
     using sum_moebius_mu_divisors' by blast
   finally show "a k m  = (if gcd m k = 1 then 1 else 0)" 
     using coprime_def by blast
 qed} note a_expr = this

  let ?f = "(\<lambda> m. (if gcd m k = 1 then 1 else 0) *
                 unity_root k (int m * n))"
  from s_k_fourier_expansion[of k id moebius_mu n] assms
  have "s (\<lambda>x. of_nat (id x)) moebius_mu k n =
  (\<Sum>m\<le>k - 1.
      1 / of_nat k *
      (\<Sum>d | d dvd gcd m k.
         moebius_mu d * of_nat (k div d) * of_nat d) *
      unity_root k (int m * n))" by simp
  also have "... = (\<Sum>m\<le>k - 1.
      a k m *
      unity_root k (int m * n))" using a_def by blast
  also have "... = (\<Sum>m\<le>k - 1.
      (if gcd m k = 1 then 1 else 0) *
      unity_root k (int m * n))" using a_expr by auto
  also have "... = (\<Sum>m \<in> {1..k}.
      (if gcd m k = 1 then 1 else 0) *
      unity_root k (int m * n))"
  proof -    
    have "periodic (\<lambda> m. (if gcd m k = 1 then 1 else 0) *
                 unity_root k (int m * n)) k"
    proof -
      have "periodic (\<lambda> m. if gcd m k = 1 then 1 else 0) k"
        by(simp add: periodic_def)
      moreover have "periodic (\<lambda> m. unity_root k (int m * n)) k" 
        using unity_periodic_mult 
        by (metis (no_types, lifting) mod_add_self2 periodic_def unity_mod unity_pow zmod_int)      
      ultimately show "periodic ?f k"
        using mult_periodic by simp
    qed
    then have "sum ?f {0..k - 1} = sum ?f {1..k}"
      using periodic_sum_periodic_shift[of ?f k 1] by force
    then show ?thesis by (simp add: atMost_atLeast0)    
  qed  
  also have "... = (\<Sum>m | m \<in> {1..k} \<and> gcd m k = 1.
                  (if gcd m k = 1 then 1 else 0) *     
                  unity_root k (int m * int n))"
    by(intro sum.mono_neutral_right,auto)
  also have "... = (\<Sum>m | m \<in> {1..k} \<and> gcd m k = 1.
                  unity_root k (int m * int n))" by simp    
  also have "... = (\<Sum>m | m \<in> {1..k} \<and> coprime m k.
                  unity_root k (int m * int n))"
    using coprime_iff_gcd_eq_1 by presburger
  also have "... = c k n" unfolding ramanujan_def by simp
  finally show ?thesis unfolding s_def by auto
qed

corollary c_k_s_form:
 "k > 0 \<Longrightarrow> c k n = s id moebius_mu k n"
  using c_k_dirichlet_form unfolding s_def by simp

subsection \<open>Multiplicative properties\<close>

print_locale multiplicative_function
(* see existing multiplicative_function *)
definition "multiplicative f = 
  ((\<forall> a b. coprime a b \<longrightarrow> f(a*b) = f(a)*f(b)) \<and> f(1) \<noteq> 0)" 
  for f :: "nat \<Rightarrow> complex"

lemma mult_unit:
  assumes "multiplicative f"
  shows "f(1) = 1" 
proof -
  have eq: "coprime 1 1" by simp
  have "f(1) = f(1*1)" by simp
  then have "f(1) = f(1) * f(1)"
    using assms eq unfolding multiplicative_def by fastforce
  then show "f(1) = 1" 
    using assms unfolding multiplicative_def by simp
qed

lemma mult_id: "multiplicative id" unfolding multiplicative_def by simp

lemma mult_moebius: "multiplicative moebius_mu"
  unfolding multiplicative_def
  using moebius_mu.mult_coprime by auto

lemma multipl_prod: 
  fixes m k d1 d2 :: nat and f :: "nat \<Rightarrow> complex"
  assumes "multiplicative f" "d1 dvd m" "d2 dvd k" "coprime m k"
  shows "f (d1*d2) = f(d1) * f(d2)"
  using assms
  unfolding multiplicative_def 
  using coprime_divisors by blast

lemma multipl_div: 
  fixes m k d1 d2 :: nat and f :: "nat \<Rightarrow> complex"
  assumes "multiplicative f" "d1 dvd m" "d2 dvd k" "coprime m k"
  shows "f ((m*k) div (d1*d2)) = f(m div d1) * f(k div d2)"
  using assms
  unfolding multiplicative_def 
  by (metis coprime_divisors div_mult_div_if_dvd dvd_mult_div_cancel dvd_triv_right)

theorem s_mult_preservation:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "a > 0" "b > 0" "m > 0" "k > 0" (* remove cond. on m,n *)
  assumes "coprime a k" "coprime b m" "coprime k m"
  assumes "multiplicative f" and "multiplicative g"
  shows "s f g (m*k) (a*b) = (s f g m a)*(s f g k b)"
proof -
  from assms(1-6) have eq: "gcd (m*k) (a*b) = gcd a m * gcd k b"
   by (simp add: linear_gcd  gcd.commute mult.commute)
  have "s f g (m*k) (a*b) = 
        (\<Sum> d | d dvd gcd (m*k) (a*b). f(d) * g((m*k) div d))"
    unfolding s_def using gcd.commute by metis
  also have "... = 
     (\<Sum> d | d dvd gcd a m * gcd k b. f(d) * g((m*k) div d))"
    using eq by simp
  also have "... = 
     (\<Sum> (d1,d2) | d1 dvd gcd a m \<and>  d2 dvd gcd k b. 
          f(d1*d2) * g((m*k) div (d1*d2)))" 
  proof -
    have b: "bij_betw (\<lambda>(d1, d2). d1 * d2)
   {(d1, d2). d1 dvd gcd a m \<and> d2 dvd gcd k b}
   {d. d dvd gcd a m * gcd k b}" 
      using assms(5) reindex_product_bij by blast
    have "(\<Sum> (d1, d2) | d1 dvd gcd a m \<and> d2 dvd gcd k b.
     f (d1 * d2) * g (m * k div (d1 * d2))) = 
      (\<Sum>x\<in>{(d1, d2). d1 dvd gcd a m \<and> d2 dvd gcd k b}.
     f (case x of (d1, d2) \<Rightarrow> d1 * d2)*
       g (m * k div (case x of (d1, d2) \<Rightarrow> d1 * d2)))"
        by(rule sum.cong,auto)
      also have "... = (\<Sum>d | d dvd gcd a m * gcd k b. f d * g (m * k div d))"
        using b by(rule sum.reindex_bij_betw[of "\<lambda> (d1,d2). d1*d2" ])
      finally show ?thesis by argo     
    qed 
  also have "... = (\<Sum> d1 | d1 dvd gcd a m.
     (\<Sum> d2 |  d2 dvd gcd k b. 
          f(d1*d2) * g((m*k) div (d1*d2))))"
      by (simp add: sum.cartesian_product)(rule sum.cong,auto) 
    also have "... = (\<Sum> d1 | d1 dvd gcd a m.
     (\<Sum> d2 |  d2 dvd gcd k b. 
          f(d1) * f(d2) * g((m*k) div (d1*d2))))"
      apply(rule sum.cong,blast, rule sum.cong, blast)   
      using assms(7-8) multipl_prod
      by (metis (no_types, lifting) gcd_nat.bounded_iff mem_Collect_eq mult.commute)
    also have "... = (\<Sum> d1 | d1 dvd gcd a m.
     (\<Sum> d2 |  d2 dvd gcd k b. 
          f(d1) * f(d2) * g(m div d1) * g(k div d2)))"
    proof -
      {fix d1 d2
      assume "d1 dvd gcd a m" "d2 dvd gcd k b"
      then have "g (m * k div (d1 * d2)) = g(m div d1) * g(k div d2)" 
        using assms(7,9) multipl_div 
        by (meson coprime_commute dvd_gcdD1 dvd_gcdD2) } note eq = this
      show ?thesis 
        apply(rule sum.cong,blast,rule sum.cong,blast)
        using eq by auto
    qed
    also have "... = 
        (\<Sum>i\<in>{d1. d1 dvd gcd a m}.
     \<Sum>j\<in>{d2. d2 dvd gcd k b}.
       f i * g (m div i) * (f j * g (k div j)))"
      by(rule sum.cong,blast,rule sum.cong,blast,simp)   
    also have "... = (\<Sum>d1 | d1 dvd gcd a m. f d1 * g (m div d1)) *
          (\<Sum>d2 | d2 dvd gcd k b. f d2 * g (k div d2))"
      using  sum_product[of 
          "\<lambda> d1. f(d1) * g(m div d1)" _
          "\<lambda> d2. f(d2) * g(k div d2)"
          ] by simp 
    also have "... = s f g m a * s f g k b"
      unfolding s_def 
      by (simp add: gcd.commute)
    finally show ?thesis by blast
qed

corollary s_m_a_b:
 fixes f g :: "nat \<Rightarrow> complex"
 assumes "a > 0" "b > 0" "m > 0" (* remove cond. on m,n *)
 assumes "coprime b m"
 assumes "multiplicative f" and "multiplicative g"
 shows "s f g m (a*b) = s f g m a"
proof -
  have "s f g m (a*b) = s f g m a * s f g 1 b"
    using assms s_mult_preservation[of a b m 1 f g] by simp
  also have "... = s f g m a * f 1 * g 1"
    using s_1_n  by auto
  also have "... = s f g m a"
    using mult_unit[of f] mult_unit[of g] assms(5-6) by auto
  finally show "s f g m (a*b) = s f g m a" by blast
qed

corollary s_mk_a:
 fixes f g :: "nat \<Rightarrow> complex"
 assumes "a > 0" "k > 0" "m > 0" (* remove cond. on m,n *)
 assumes "coprime a k" and "coprime k m"
 assumes "multiplicative f" and "multiplicative g"
 shows "s f g (m*k) a = s f g m a * g k"
proof -
  have "s f g (m*k) a = s f g m a * s f g k 1"
    using assms s_mult_preservation[of a 1 m k f g] by simp
  also have "... = s f g m a * f(1) * g(k)" 
    using s_k_1 by auto
  also have "... = s f g m a *  g k" 
    using mult_unit[of f] assms(6) by auto
  finally show ?thesis by blast
qed

corollary multi_c_mk_ab:
 assumes "a > 0" "k > 0" "m > 0" "b > 0" (* remove cond. on m,n *)
 assumes "coprime a k" "coprime b m" "coprime m k"
 shows "c (m*k) (a*b) = c m a * c k b"
proof -
  have "c (m*k) (a*b) = s id moebius_mu (m*k) (a*b)" 
    using c_k_s_form assms(2,3) by simp
  also have "... = (s id moebius_mu m a) * (s id moebius_mu k b)"
    using s_mult_preservation[of a b m k id moebius_mu]
          assms mult_id mult_moebius coprime_commute[of m k]
    by simp
  also have "... = c m a * c k b" using c_k_s_form assms by simp
  finally show ?thesis by simp
qed

corollary multi_c_m:
 assumes "a > 0" "k > 0" "m > 0" "b > 0" (* remove cond. on m,n *)
 assumes "coprime b m" 
 shows "c m (a*b) = c m a"
  using assms c_k_s_form mult_id mult_moebius s_m_a_b by auto

corollary multi_c_mk:
 assumes "a > 0" "k > 0" "m > 0" "b > 0" (* remove cond. on m,n *)
 assumes "coprime a k" "coprime m k" 
 shows "c (m*k) a = c m a * moebius_mu k"
  using assms
  by (metis c_k_1 coprime_1_left mult.commute mult.left_neutral multi_c_mk_ab zero_less_one)

definition "c_multiplicative f = 
  ((\<forall> a b. f(a*b) = f(a)*f(b)) \<and> f(1) \<noteq> 0)" 
  for f :: "nat \<Rightarrow> complex"


lemma 
  fixes f :: "nat \<Rightarrow> complex"
  shows "(\<Sum> d | d dvd n. moebius_mu d * f d) = 
         (\<Prod> p | prime p \<and> p dvd n. 1 - f(p))"

 thm dirichlet_inverse

theorem
  fixes f h :: "nat \<Rightarrow> complex" and n k :: nat
  defines "g \<equiv> (\<lambda> k. moebius_mu k * h k)" 
  defines "F \<equiv> dirichlet_prod f g"
  defines "N \<equiv> k div gcd n k" 
  assumes "c_multiplicative f" "multiplicative h" 
  assumes "prime p \<Longrightarrow> f(p) \<noteq> 0 \<and> f(p) \<noteq> h(p)"
  shows "s f g k n = (F(k)*g(N)) div (F(N))"
proof -
  have "F(k) = dirichlet_prod g f k"
    unfolding F_def using dirichlet_prod_commutes by metis

  also have "... = (\<Sum> d | d dvd k. f(k div d) * moebius_mu d * h d)"
    
qed

end