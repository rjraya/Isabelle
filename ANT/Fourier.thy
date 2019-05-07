theory Fourier
  imports 
    "HOL-Number_Theory.Number_Theory"
    "HOL-Analysis.Analysis"
    Dirichlet_L.Dirichlet_Characters
    Dirichlet_Series.More_Totient
    Dirichlet_Series.Moebius_Mu
    Polynomial_Interpolation.Lagrange_Interpolation
    Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
begin

section\<open>Sums and products\<close>

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

lemma prod_div_add:
  fixes f :: "nat \<Rightarrow> complex"
  assumes "finite A" "finite B" "A \<inter> B = {}"
  shows "(\<Prod> i \<in> A \<union> B. f i) = ((\<Prod> i \<in> A. f i) * (\<Prod> i \<in> B. f i))"
  by (simp add: assms prod.union_disjoint)

lemma prod_div_sub:
  fixes f :: "nat \<Rightarrow> complex"
  assumes "finite A" "B \<subseteq> A" "\<forall> b \<in> B. f b \<noteq> 0"
  shows "(\<Prod> i \<in> A - B. f i) = ((\<Prod> i \<in> A. f i) div (\<Prod> i \<in> B. f i))"
  using assms
proof(induction "card B" arbitrary: B)
case 0
  then show ?case 
    using infinite_super by fastforce
next
  case (Suc n)
  then show ?case 
  proof -
    obtain B' x where decomp: "B = B' \<union> {x} \<and> x \<notin> B'" 
      using Suc(2) 
      by (metis card_eq_SucD inf_sup_aci(5) insert_is_Un)
    then have B'card: "card B' = n" using Suc(2) 
      using Suc.prems(2) assms(1) finite_subset by fastforce
    have "prod f (A - B) = prod f ((A-B') - {x})"
      using decomp 
      by (metis Diff_insert Un_insert_right sup_bot.right_neutral)
    also have "... = (prod f (A-B')) div f x"  
      using prod_diff1[of "A-B'" f x] Suc decomp by auto
    also have "... = (prod f A div prod f B') div f x"
      using Suc(1)[of B'] Suc(3) B'card decomp
            Suc.prems(2) Suc.prems(3) by force
    also have "... = prod f A div (prod f B' * f x)"
      by auto
    also have "... = prod f A div prod f B"
      using decomp Suc.prems(2) assms(1) finite_subset by fastforce
    finally show ?thesis by blast
  qed
qed 

lemma sum_over_classes:
  fixes f :: "nat \<Rightarrow> nat" and g :: "nat \<Rightarrow> complex"
  assumes  "finite A" 
  assumes "\<forall> y \<in> f ` A. card {x \<in> A. f(x) = y} = n"
  shows "sum (\<lambda> k. g(f(k))) A = sum (\<lambda> k. n*g k) (f ` A)"
proof -
  {fix y
  assume as: "y \<in> f ` A" 
  have "(\<Sum>k\<in>{x \<in> A. f x = y}. g (f k)) = n* g y"
    by(simp, subst assms(2), auto simp add: as)}
  note inner_sum = this
  thm inner_sum
  have "sum (\<lambda> k. g(f(k))) A = (\<Sum>y\<in>f ` A. \<Sum>k\<in>{x \<in> A. f x = y}. g (f k))" 
    using sum_image_gen[of A "(\<lambda> k. g(f(k)))" f] assms(1) by blast
  also have "... = (\<Sum>y\<in>f ` A. n * g (y))" 
  proof(rule sum.cong,simp)
    fix x
    assume lo: "x \<in> f ` A"
    show "(\<Sum>k\<in>{xa \<in> A. f xa = x}. g (f k)) = of_nat n * g x"     
      by(subst inner_sum,simp add: lo,simp)
  qed
  finally show ?thesis by blast
qed

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

lemma self_bij_0_k:
  fixes a k :: nat
  assumes "coprime a k" "[a*i = 1] (mod k)" "k > 0" 
  shows "bij_betw (\<lambda> r. r*a mod k) {0..k-1} {0..k-1}"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda> r. r*a mod k) {0..k-1}"
  proof -
    {fix r1 r2
    assume in_k: "r1 \<in> {0..k-1}" "r2 \<in> {0..k-1}"
    assume as: "[r1*a = r2*a] (mod k)"
    then have "[r1*a*i = r2*a*i] (mod k)" 
      using cong_scalar_right by blast
    then have "[r1 = r2] (mod k)" 
      using cong_mult_rcancel_nat as assms(1) by simp
    then have "r1 = r2" using in_k
      using assms(3) cong_less_modulus_unique_nat by auto}
    note eq = this
    show ?thesis unfolding inj_on_def 
      by(safe, simp add: eq cong_def)
  qed
  define f where "f = (\<lambda>r. r * a mod k)"
  show "f ` {0..k - 1} = {0..k - 1} "
    unfolding image_def
  proof(standard)
    show "{y. \<exists>x\<in>{0..k - 1}. y = f x} \<subseteq> {0..k - 1}" 
    proof -
      {fix y
      assume "y \<in> {y. \<exists>x\<in>{0..k - 1}. y = f x}" 
      then obtain x where "y = f x" by blast
      then have "y \<in> {0..k-1}"
        unfolding f_def
        using Suc_pred assms(3) lessThan_Suc_atMost by fastforce}
      then show ?thesis by blast
    qed
    show "{0..k - 1} \<subseteq> {y. \<exists>x\<in>{0..k - 1}. y = f x}"
    proof -
      {fix x 
        assume ass: "x \<in> {0..k-1}"
        then have "x * i mod k \<in> {0..k-1}"
          by (metis One_nat_def Suc_pred assms(3) atMost_atLeast0 atMost_iff less_Suc_eq_le mod_less_divisor)
        then have "f (x * i mod k) = x"
        proof -
          have "f (x * i mod k) = (x * i mod k) * a mod k"
            unfolding f_def by blast
          also have "... = (x*i*a) mod k" 
            by (simp add: mod_mult_left_eq) 
          also have "... = (x*1) mod k" 
            using assms(2) unfolding cong_def 
            by (metis mod_mult_right_eq mult.assoc mult.commute)
          also have "... = x" using ass assms(3) by auto
          finally show ?thesis .
        qed
        then have "x \<in> {y. \<exists>x\<in>{0..k - 1}. y = f x}" 
          using \<open>x * i mod k \<in> {0..k - 1}\<close> by force}
      then show ?thesis by blast 
    qed
  qed
qed

lemma periodic_homothecy:
  assumes "periodic f k"
  shows "periodic (\<lambda> l. f(l*a)) k"
  unfolding periodic_def
proof 
  fix n
  have "f ((n + k) * a) = f(n*a+k*a)" by(simp add: algebra_simps)
  also have "... = f(n*a)" 
    using mult_period[OF assms] unfolding periodic_def by simp
  finally show "f ((n + k) * a) = f (n * a)" by simp
qed

theorem periodic_remove_homothecy:
  assumes "coprime a k" "periodic f k" "k > 0" 
  shows "(\<Sum> l = 1..k. f(l)) = (\<Sum> l = 1..k. f(l*a))" 
proof -
  obtain i where inv: "[a*i = 1] (mod k)"
    using assms(1) coprime_iff_invertible_nat[of a k] by auto
  from this self_bij_0_k assms
  have bij: "bij_betw (\<lambda>r. r * a mod k) {0..k - 1} {0..k - 1}" by blast
  
  have "(\<Sum> l = 1..k. f(l)) = (\<Sum> l = 0..k-1. f(l))"
    using periodic_sum_periodic_shift[of f k 1] assms by simp
  also have "... = (\<Sum> l = 0..k-1. f(l*a mod k))"
    using sum.reindex_bij_betw[OF bij] by metis
  also have "... = (\<Sum> l = 0..k-1. f(l*a))"
    apply(rule sum.cong,simp)
    using mod_periodic[OF assms(2)] mod_mod_trivial by blast
  also have "... = (\<Sum> l = 1..k. f(l*a))"
    using periodic_sum_periodic_shift[of "(\<lambda> l. f(l*a))" k 1]
          periodic_homothecy[OF assms(2)] assms(3) by fastforce  
  finally show ?thesis by blast     
qed

section\<open>Gcd and prime factorizations\<close>

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

lemma p_div_set:
  shows "{p. p \<in>prime_factors a \<and> \<not> p dvd N} = 
          ({p. p \<in>prime_factors (a*N)} - {p. p \<in>prime_factors N})"
     (is "?A = ?B") 
proof 
   show "?A \<subseteq> ?B" 
   proof(simp)
     {fix p 
     assume as: "p \<in># prime_factorization a \<and> \<not> p dvd N"
     then have 1: "p \<in> prime_factors (a * N)" 
       by (metis divisors_zero dvdI dvd_trans in_prime_factors_iff)
     from as have 2: "p \<notin> prime_factors N" by blast
     from 1 2 have "p \<in> prime_factors (a * N) - prime_factors N"
       by blast}
     then show "{p. p \<in># prime_factorization a \<and> \<not> p dvd N}
    \<subseteq> prime_factors (a * N) - prime_factors N" by blast
   qed

   show "?B \<subseteq> ?A"
   proof(simp)
     {fix p 
     assume as: "p \<in> prime_factors (a * N) - prime_factors N"
     then have 1: "\<not> p dvd N" 
       by (metis DiffE in_prime_factors_imp_prime mult.commute mult_eq_0_iff prime_factorization_empty_iff prime_factorsI  set_mset_empty)
     from as have 2: "p \<in># prime_factorization a" 
       by (metis DiffD1 \<open>\<not> p dvd N\<close> in_prime_factors_iff mult_eq_0_iff prime_dvd_multD)
     from 1 2 have "p \<in> {p. p \<in># prime_factorization a \<and> \<not> p dvd N}" by blast}
   then show " prime_factors (a * N) - prime_factors N
    \<subseteq> {p. p \<in># prime_factorization a \<and> \<not> p dvd N}" by blast
   qed
 qed


(*exercise 8.4*)
lemma technical_m:
  fixes n a d :: nat
  assumes 0: "n > 0" 
  assumes 1: "coprime a d"
  assumes 2: "m = a + q*d" 
  assumes 3: "q \<equiv> (\<Prod> p | prime p \<and> p dvd n \<and> \<not> (p dvd a). p)"
  shows "[m = a] (mod d)" "coprime m n"
proof(simp add: 2 cong_add_lcancel_0_nat cong_mult_self_right)
  have fin: "finite {p. prime p \<and> p dvd n \<and> \<not> (p dvd a)}" by (simp add: "0")
  {fix p
  assume 4: "prime p" "p dvd m" "p dvd n"
  have "p = 1"
  proof(cases "p dvd a")
    case True
    from this 2 4(2) have "p dvd q*d" 
      by (simp add: dvd_add_right_iff)
    then have a1: "p dvd q \<or> p dvd d"
      using 4(1) prime_dvd_mult_iff by blast
    
    have a2: "\<not> (p dvd q)" 
    proof(rule ccontr,simp)  
      assume "p dvd q"
      then have "p dvd (\<Prod> p | prime p \<and> p dvd n \<and> \<not> (p dvd a). p)" unfolding 3 by simp
      then have "\<exists>x\<in>{p. prime p \<and> p dvd n \<and> \<not> p dvd a}. p dvd x"
        using prime_dvd_prod_iff[OF fin 4(1)] by simp
      then obtain x where c: "p dvd x \<and> prime x \<and> \<not> x dvd a" by blast
      then have "p = x" using 4(1) by (simp add: primes_dvd_imp_eq)
      then show "False" using True c by auto
    qed
    have a3: "\<not> (p dvd d)" using True "1" "4"(1) coprime_def not_prime_unit by auto
  
    from a1 a2 a3 show ?thesis by simp
  next
    case False
    then have "p dvd q" 
    proof -
      have in_s: "p \<in> {p. prime p \<and> p dvd n \<and> \<not> p dvd a}"
        using False 4(3) 4(1) by simp
      show "p dvd q" 
        unfolding 3 using dvd_prodI[OF fin in_s ] by fast
    qed
    then have "p dvd q*d" by simp
    then have "p dvd a" using 4(2) 2 by (simp add: dvd_add_left_iff)
    then show ?thesis using False by auto
  qed}
  then show "coprime m n" 
    by (metis coprime_iff_gcd_eq_1 gcd_nat.bounded_iff not_prime_1 prime_factor_nat)
qed

lemma chinese_solution:
  fixes r d k :: nat
  assumes "r \<noteq> 0" "d \<noteq> 0" "coprime r d" "d dvd k" "k \<noteq> 0"
  shows "\<exists> n. [n = r] (mod d) \<and> coprime n k"
proof -
  define k' where "k' = \<Prod> {p. prime p \<and> p dvd k \<and> \<not> p dvd d}"
  have "coprime k' d" 
    unfolding k'_def 
    by (metis (no_types, lifting) mem_Collect_eq prime_imp_coprime_nat prod_coprime_left)
  then have "coprime d k'" using coprime_commute[of k' d] by blast
  have "k' \<noteq> 0" 
    unfolding k'_def 
    by (metis (no_types, lifting) mem_Collect_eq not_prime_0 prod.infinite prod_zero_iff zero_neq_one)
  from chinese_remainder[of d k' r 1, OF \<open>coprime d k'\<close> assms(2) \<open>k' \<noteq> 0\<close>]
  obtain x q1 q2 where "x = r + q1 * d \<and> x = 1 + q2 * k'" by blast
  then have eq: "[x = r] (mod d) \<and> [x = 1] (mod k')" 
    by (metis cong_add_lcancel_0_nat cong_to_1'_nat)
  then have cop: "coprime x k" 
  proof -
   have "coprime x k'" using eq 
     using cong_imp_coprime_nat cong_sym coprime_1_left by blast
   have "coprime x d" using eq 
     using assms(3) cong_imp_coprime_nat cong_sym by blast 
   have "\<forall> p. prime p \<and> p dvd k \<longrightarrow> coprime x p" 
     unfolding k'_def
   proof(safe)
     fix p 
     assume "prime p" "p dvd k" 
     then show "coprime x p" 
     proof(cases "p dvd d")
       case True then show ?thesis using \<open>coprime x d\<close> by auto
     next
       case False
       then show ?thesis  
       proof -
         have "p \<in> {p. prime p \<and> p dvd k \<and> \<not> p dvd d}"
           using \<open>prime p\<close> \<open>p dvd k\<close> False by auto
         then have "p dvd k'" unfolding k'_def
         proof -           
           have "finite {p. prime p \<and> p dvd k \<and> \<not> p dvd d}" 
             using assms(5) by auto
           from prod_dvd_prod_subset[of "{p. prime p \<and> p dvd k \<and> \<not> p dvd d}" "{p}" id, 
                OF this, simplified]
           have "prod id {p} dvd prod id {p. prime p \<and> p dvd k \<and> \<not> p dvd d}" 
             using \<open>prime p\<close> \<open>p dvd k\<close> \<open>\<not> p dvd d\<close> by simp
           then show "p dvd \<Prod>{p. prime p \<and> p dvd k \<and> \<not> p dvd d}" by simp
         qed
         then show "coprime x p" using \<open>coprime x k'\<close> k'_def by fastforce
       qed
     qed
   qed
   note lem = this
   {fix p
   have "prime p \<Longrightarrow> p dvd x \<Longrightarrow> p dvd k \<Longrightarrow> p = 1"
     using lem by (meson coprime_absorb_right dvd_antisym one_dvd)
   } then show "coprime x k" (* generalize this argument, also apears in technical_m *)
    by (metis coprime_iff_gcd_eq_1 gcd_nat.bounded_iff not_prime_1 prime_factor_nat)    
  qed
  show ?thesis using cop eq by blast
qed

lemma double_finite_surj:
  fixes f :: "nat \<Rightarrow> nat" and A B :: "nat set"
  assumes "finite A" "finite B" 
          "f ` A = B" "g ` B = A"
  shows "card A = card B"
  using assms 
  by (metis card_image_le le_antisym)

lemma 
  assumes "d dvd m" "m > 1" "d > 0" 
  assumes "y \<in> totatives d" 
  shows "card {x \<in> totatives m. [x = y] (mod d)} = 
         card {x \<in> totatives m. [x = 1] (mod d)}"
proof -
  let ?A = "{x \<in> totatives m. [x = y] (mod d)}"
  let ?B = "{x \<in> totatives m. [x = 1] (mod d)}"
  assume "d dvd m" "m > 1" "d > 0" 
  assume y_tot: "y \<in> totatives d" 
  then have y_cop: "coprime y d" unfolding totatives_def by blast
  then obtain y' where y'_def: "[y'*y = 1] (mod d)" 
    by (metis cong_solve mult.commute)
  have y_not_0: "y \<noteq> 0" using y_tot unfolding totatives_def by auto
  have d_not_0: "d \<noteq> 0" using assms(3) by blast
  have m_not_0: "m \<noteq> 0" using assms(2) by auto
  let ?f = "\<lambda> x. y'*x"
  let ?g = "\<lambda> x. y*x"
  have 1: "finite ?A" by simp
  have 2: "finite ?B" by simp
  have 3: "?f ` ?A = ?B" 
  proof -
    fix t
    assume "t \<in> ?B"
    then have "t \<in> totatives m \<and> [t = 1] (mod d)" by auto
    then have "\<exists> x \<in> ?A. y'*x = t" 
    proof -
      from  chinese_solution[of y d m, 
           OF y_not_0 d_not_0 y_cop assms(1) 
           m_not_0]
      obtain n where "[n = y] (mod d) \<and> coprime n m" by blast
      
    qed
    thm chinese_solution[] assms
  qed
    sorry

    have 4: "?g ` ?B = ?A" sorry
  
    from double_finite_surj[OF 1 2 3 4]
    show "card {x \<in> totatives m. [x = y] (mod d)} = 
         card {x \<in> totatives m. [x = 1] (mod d)}"


 
  have "bij_betw (\<lambda> x. (y*x) mod d)
                 {x \<in> totatives m. [x = 1] (mod d)} 
                 {x \<in> totatives m. [x = y] (mod d)}"
    unfolding bij_betw_def
  proof
    show "inj_on (\<lambda>x. y * x mod d)
     {x \<in> totatives m. [x = 1] (mod d)}" 
      unfolding inj_on_def
    proof(safe)
      fix x z
      assume "x \<in> totatives m" "[x = 1] (mod d)"
      assume "z \<in> totatives m" "[z = 1] (mod d)"
      assume "y * x mod d = y * z mod d" 
      then have "[y*x = y*z] (mod d)" using cong_def by blast
      then have "[y'*y*x = y'*y*z] (mod d)" using cong_mult_lcancel_nat cong_scalar_left y_cop by blast
      then have "[x = z] (mod d)" using y'_def using \<open>[y * x = y * z] (mod d)\<close> cong_mult_lcancel_nat y_cop by blast
      then show "x = z" 
      proof -

      qed
    qed
qed

section \<open>Moebius\<close>

lemma moebius_not_c:
  assumes "\<not> coprime N d"
  shows "moebius_mu (N*d) = 0"
  using assms
  unfolding moebius_mu_def squarefree_def coprime_def
  by (metis mult_dvd_mono power2_eq_square)

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

find_theorems "cnj (exp _)"
find_theorems "cnj  \<i> "
lemma "cnj (a*\<i>) = -a*\<i>" for a :: real
  by simp

lemma unity_cnj: "cnj (unity_root k m) = unity_root k (-m)" 
  unfolding unity_exp exp_cnj by simp  

lemma unity_div_num:
  assumes "k > 0" "d > 0" "d dvd k"
  shows "unity_root k (x * (k div d)) = unity_root d x"
  using assms dvd_div_mult_self unity_div by auto
 

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

lemma mult_id: "multiplicative_function id" 
  by (simp add: multiplicative_function_def)

lemma mult_moebius: "multiplicative_function moebius_mu"
  using Moebius_Mu.moebius_mu.multiplicative_function_axioms
  by simp

lemma mult_of_nat: "multiplicative_function of_nat" 
  using multiplicative_function_def of_nat_0 of_nat_1 of_nat_mult by blast

lemma mult_of_nat_c: "completely_multiplicative_function of_nat" 
  by (simp add: completely_multiplicative_function_def)

lemma non_zero_c:
  fixes f :: "nat \<Rightarrow> complex"
  assumes "completely_multiplicative_function f" 
          "d \<noteq> 0"
          "\<And> p. prime p \<Longrightarrow> f(p) \<noteq> 0" 
  shows "f(d) \<noteq> 0"
  using assms(2)
proof(induction d rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof(cases "n = 1")
    case True
    then show ?thesis 
      using assms(1)
      unfolding completely_multiplicative_function_def by simp
  next
    case False
    then obtain p where 2:"prime p \<and> p dvd n" 
      using prime_factor_nat by blast
    then obtain a where 3: "n = p * a \<and> a \<noteq> 0" 
      using 1 by (metis dvdE mult_0_right)
    then have 4: "f(a) \<noteq> 0" using 1 
      using 2 prime_nat_iff by fastforce
    have 5: "f(p) \<noteq> 0" using assms(3) 2 by simp
    from 3 4 5 show ?thesis
      by (simp add: assms(1) completely_multiplicative_function.mult)
  qed
qed

lemma multipl_prod:
  fixes m k d1 d2 :: nat and f :: "nat \<Rightarrow> complex"
  assumes "multiplicative_function f" "d1 dvd m" "d2 dvd k" "coprime m k"
  shows "f (d1*d2) = f(d1) * f(d2)"
  by (meson assms coprime_divisors multiplicative_function.mult_coprime)

lemma multipl_div: 
  fixes m k d1 d2 :: nat and f :: "nat \<Rightarrow> complex"
  assumes "multiplicative_function f" "d1 dvd m" "d2 dvd k" "coprime m k"
  shows "f ((m*k) div (d1*d2)) = f(m div d1) * f(k div d2)"
  using assms
  unfolding multiplicative_function_def
  using assms(1) multiplicative_function.mult_coprime by fastforce

lemma multipl_div_c: 
  fixes m k d1 d2 :: nat and f :: "nat \<Rightarrow> complex"
  assumes "completely_multiplicative_function f" 
          "d1 dvd m" "d2 dvd k" 
  shows "f ((m*k) div (d1*d2)) = f(m div d1) * f(k div d2)"
  using assms
proof -
  have "f ((m*k) div (d1*d2)) = f((m div d1) * (k div d2))"
    using assms(2,3) by fastforce
  also have "... = f(m div d1) * f(k div d2)"
    using assms unfolding completely_multiplicative_function_def
    by (simp,metis One_nat_def le_eq_less_or_eq less_Suc0 mult.left_neutral mult.right_neutral mult_zero_left mult_zero_right not_le)
  finally show ?thesis by simp
qed

lemma multipl_div_mono: 
  fixes m k d :: nat and f :: "nat \<Rightarrow> complex"
  assumes "completely_multiplicative_function f" 
          "d dvd k" "d > 0" 
          "\<And> p. prime p \<Longrightarrow> f(p) \<noteq> 0" 
  shows "f (k div d) = f(k) div f(d)"
proof -
  have "d \<noteq> 0" using assms(2,3) by auto
  then have nz: "f(d) \<noteq> 0" using assms(1,4) non_zero_c by simp

  from assms(2,3) obtain a where div: "k = a * d "
    by fastforce
  have "f (k div d) = f ((a*d) div d)" using div by simp
  also have "... = f(a)" 
    using assms(3) div by simp
  also have "... = f(a)*f(d) div f(d)" 
    using nz by auto
  also have "... = f(a*d) div f(d)" 
    by (simp add: div assms(1) completely_multiplicative_function.mult)
  also have "... = f (k) div f(d)" using div by simp
  finally show ?thesis by simp
qed

lemma comp_to_mult: "completely_multiplicative_function f \<Longrightarrow>
       multiplicative_function f"
  unfolding completely_multiplicative_function_def
            multiplicative_function_def by auto

theorem s_mult_preservation:
  fixes f g :: "nat \<Rightarrow> complex"
  assumes "a > 0" "b > 0" "m > 0" "k > 0" (* remove cond. on m,n *)
  assumes "coprime a k" "coprime b m" "coprime k m"
  assumes "multiplicative_function f" and 
          "multiplicative_function g"
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
 assumes "multiplicative_function f" and 
         "multiplicative_function g"
 shows "s f g m (a*b) = s f g m a"
proof -
  have "s f g m (a*b) = s f g m a * s f g 1 b"
    using assms s_mult_preservation[of a b m 1 f g] by simp
  also have "... = s f g m a * f 1 * g 1"
    using s_1_n  by auto
  also have "... = s f g m a"
    using  assms(5-6) 
    by (simp add: multiplicative_function_def)
  finally show "s f g m (a*b) = s f g m a" by blast
qed

corollary s_mk_a:
 fixes f g :: "nat \<Rightarrow> complex"
 assumes "a > 0" "k > 0" "m > 0" (* remove cond. on m,n *)
 assumes "coprime a k" and "coprime k m"
 assumes "multiplicative_function f" and 
         "multiplicative_function g"
 shows "s f g (m*k) a = s f g m a * g k"
proof -
  have "s f g (m*k) a = s f g m a * s f g k 1"
    using assms s_mult_preservation[of a 1 m k f g] by simp
  also have "... = s f g m a * f(1) * g(k)" 
    using s_k_1 by auto
  also have "... = s f g m a *  g k" 
    using assms(6)
    by(simp add: multiplicative_function_def)
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
          assms mult_id mult_moebius mult_of_nat         
          coprime_commute[of m k] by auto
  also have "... = c m a * c k b" using c_k_s_form assms by simp
  finally show ?thesis by simp
qed

corollary multi_c_m:
 assumes "a > 0" "k > 0" "m > 0" "b > 0" (* remove cond. on m,n *)
 assumes "coprime b m" 
 shows "c m (a*b) = c m a"
  using assms c_k_s_form mult_id mult_moebius 
        mult_of_nat s_m_a_b by auto

corollary multi_c_mk:
 assumes "a > 0" "k > 0" "m > 0" "b > 0" (* remove cond. on m,n *)
 assumes "coprime a k" "coprime m k" 
 shows "c (m*k) a = c m a * moebius_mu k"
  using assms
  by (metis c_k_1 coprime_1_left mult.commute mult.left_neutral multi_c_mk_ab zero_less_one)

(* TODO Remove, 2.18 *)
lemma sum_divisors_moebius_mu_times_multiplicative:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  assumes "multiplicative_function f" "n > 0"
  shows   "(\<Sum>d | d dvd n. moebius_mu d * f d) = (\<Prod>p\<in>prime_factors n. 1 - f p)"
proof -
  define g where "g = (\<lambda>n. \<Sum>d | d dvd n. moebius_mu d * f d)"
  define g' where "g' = dirichlet_prod (\<lambda>n. moebius_mu n * f n) (\<lambda>n. if n = 0 then 0 else 1)"
  interpret f: multiplicative_function f by fact
  have "multiplicative_function (\<lambda>n. if n = 0 then 0 else 1 :: 'a)"
    by standard auto
  interpret multiplicative_function g' unfolding g'_def
    by (intro multiplicative_dirichlet_prod multiplicative_function_mult
              moebius_mu.multiplicative_function_axioms assms) fact+

  have g'_primepow: "g' (p ^ k) = 1 - f p" if "prime p" "k > 0" for p k
  proof -
    have "g' (p ^ k) = (\<Sum>i\<le>k. moebius_mu (p ^ i) * f (p ^ i))"
      using that by (simp add: g'_def dirichlet_prod_prime_power)
    also have "\<dots> = (\<Sum>i\<in>{0, 1}. moebius_mu (p ^ i) * f (p ^ i))"
      using that by (intro sum.mono_neutral_right) (auto simp: moebius_mu_power')
    also have "\<dots> = 1 - f p"
      using that by (simp add: moebius_mu.prime)
    finally show ?thesis .
  qed

  have "g' n = g n"
    by (simp add: g_def g'_def dirichlet_prod_def)
  also from assms have "g' n = (\<Prod>p\<in>prime_factors n. g' (p ^ multiplicity p n))"
      by (intro prod_prime_factors) auto
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. 1 - f p)"
    by (intro prod.cong) (auto simp: g'_primepow prime_factors_multiplicity)
  finally show ?thesis by (simp add: g_def)
qed

lemma multiplicative_ind_coprime [intro]: "multiplicative_function (ind
(coprime N))"
  by (intro multiplicative_function_ind) auto

lemma sum_divisors_moebius_mu_times_multiplicative_revisited:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  assumes "multiplicative_function f" "n > 0" "N > 0"
  shows   "(\<Sum>d | d dvd n \<and> coprime N d. moebius_mu d * f d) =
           (\<Prod>p\<in>{p. p \<in> prime_factors n \<and> \<not> (p dvd N)}. 1 - f p)"
proof -
  have "(\<Sum>d | d dvd n \<and> coprime N d. moebius_mu d * f d) =
          (\<Sum>d | d dvd n. moebius_mu d * (ind (coprime N) d * f d))"
    using assms by (intro sum.mono_neutral_cong_left) (auto simp: ind_def)
  also have "\<dots> = (\<Prod>p\<in>prime_factors n. 1 - ind (coprime N) p * f p)"
    using assms by (intro sum_divisors_moebius_mu_times_multiplicative)
                   (auto intro: multiplicative_function_mult)
  also from assms have "\<dots> = (\<Prod>p | p \<in> prime_factors n \<and> \<not>(p dvd N). 1 -
f p)"
    by (intro prod.mono_neutral_cong_right)
       (auto simp: ind_def prime_factors_dvd coprime_commute dest:
prime_imp_coprime)
  finally show ?thesis .
qed

lemma F_form:
  fixes f h :: "nat \<Rightarrow> complex" and k :: nat
  defines "g \<equiv> (\<lambda> k. moebius_mu k * h k)" 
  defines "F \<equiv> dirichlet_prod f g"
  assumes "k > 0"
  assumes "completely_multiplicative_function f" 
          "multiplicative_function h" 
  assumes "\<And> p. prime p \<Longrightarrow> f(p) \<noteq> 0 \<and> f(p) \<noteq> h(p)" 
  shows "F(k) = f(k) * (\<Prod>p\<in>prime_factors k. 1 - (h p div f p))"
proof -
  have 1: "multiplicative_function (\<lambda> p. h(p) div f(p))"
    using multiplicative_function_divide
          comp_to_mult assms(4,5) by blast

  have "F(k) = dirichlet_prod g f k"
    unfolding F_def using dirichlet_prod_commutes by metis
  also have "... = (\<Sum> d | d dvd k. moebius_mu d * h d * f(k div d))"
    unfolding g_def dirichlet_prod_def by blast
  also have "... = (\<Sum> d | d dvd k. moebius_mu d * h d * (f(k) div f(d)))"
    using multipl_div_mono[of f _ k] assms(4,6) 
    by(intro sum.cong,auto,force)  
  also have "... = f(k) * (\<Sum> d | d dvd k. moebius_mu d * (h d div f(d)))"
    by(simp add: sum_distrib_left algebra_simps)
  also have "... = f(k) * (\<Prod>p\<in>prime_factors k. 1 - (h p div f p))"
    using sum_divisors_moebius_mu_times_multiplicative[of "\<lambda> p. h p div f p" k] 1
          assms(3) by simp
  finally show F_eq: "F(k) = f(k) * (\<Prod>p\<in>prime_factors k. 1 - (h p div f p))"
    by blast
qed

(* theorem 8.8 *)
theorem s_k_n_dirichlet_expr:
  fixes f h :: "nat \<Rightarrow> complex" and n k :: nat
  defines "g \<equiv> (\<lambda> k. moebius_mu k * h k)" 
  defines "F \<equiv> dirichlet_prod f g"
  defines "N \<equiv> k div gcd n k" 
  assumes "completely_multiplicative_function f" 
          "multiplicative_function h" 
  assumes "\<And> p. prime p \<Longrightarrow> f(p) \<noteq> 0 \<and> f(p) \<noteq> h(p)" 
  assumes "k > 0" "n > 0"  
  shows "s f g k n = (F(k)*g(N)) div (F(N))"
proof -
  define a where "a \<equiv> gcd n k" 
  have 2: "k = a*N" unfolding a_def N_def by auto
  have 3: "a > 0" using a_def assms(7,8) by simp
  have Ngr0: "N > 0" using assms(7,8) 2 N_def by fastforce
  have f_k_not_z: "f k \<noteq> 0" 
    using non_zero_c assms(4,6,7) by blast
  have f_N_not_z: "f N \<noteq> 0" 
      using non_zero_c assms(4,6) Ngr0 by blast
  have bij: "bij_betw (\<lambda> d. a div d) {d. d dvd a} {d. d dvd a}"
    unfolding bij_betw_def
  proof
    show inj: "inj_on (\<lambda> d. a div d) {d. d dvd a}"
      using inj_on_def "3" dvd_div_eq_2 by blast
    show surj: "(\<lambda> d. a div d) ` {d. d dvd a} = {d. d dvd a}"
      unfolding image_def 
    proof 
      show " {y. \<exists>x\<in>{d. d dvd a}. y = a div x} \<subseteq> {d. d dvd a}"
        by auto
      show "{d. d dvd a} \<subseteq> {y. \<exists>x\<in>{d. d dvd a}. y = a div x}"
      proof 
        fix d
        assume a: "d \<in> {d. d dvd a}"
        from a have 1: "(a div d) \<in> {d. d dvd a}" by auto
        from a have 2: "d = a div (a div d)" using 3 by auto
        from 1 2 show "d \<in> {y. \<exists>x\<in>{d. d dvd a}. y = a div x} " by blast        
      qed
    qed
  qed
  
  have "s f g k n = (\<Sum> d | d dvd a. f(d)*moebius_mu(k div d)*h(k div d))"
    unfolding s_def g_def a_def by(simp add: mult.assoc)
  also have "... = (\<Sum> d | d dvd a. f(d) * moebius_mu(a*N div d)*h(a*N div d))"
    using 2 by blast
  also have "... = (\<Sum> d | d dvd a. f(a div d) * moebius_mu(N*d)*h(N*d))"
    (is "?a = ?b")
  proof -
    define f_aux where "f_aux \<equiv> (\<lambda> d. f d * moebius_mu (a * N div d) * h (a * N div d))"
    have 1: "?a = (\<Sum>d | d dvd a. f_aux d)" using f_aux_def by blast
    {fix d :: nat
    assume "d dvd a"
    then have "N * a div (a div d) = N * d" 
      using 3 by force}
    then have 2: "?b = (\<Sum>d | d dvd a. f_aux (a div d))" 
      unfolding f_aux_def by(simp add: algebra_simps)
    show "?a = ?b" 
    using sum.reindex_bij_betw[of "((div) a)" "{d. d dvd a}" "{d. d dvd a}"]
          bij 1 2 by metis
  qed
  also have "... = moebius_mu N * h N * f a * (\<Sum> d | d dvd a \<and> coprime N d. moebius_mu d * (h d div f d))"
   (is "?a = ?b")
  proof -
    have "?a = (\<Sum> d | d dvd a \<and> coprime N d. f(a div d) * moebius_mu (N*d) * h (N*d))"
      by(rule sum.mono_neutral_right)
        (auto simp add: moebius_not_c 3)
    also have "... = (\<Sum> d | d dvd a \<and> coprime N d. moebius_mu N * h N * f(a div d) * moebius_mu d * h d)"
    proof(rule sum.cong,simp)
      fix d
      assume a: "d \<in> {d. d dvd a \<and> coprime N d}"
      then have 1: "moebius_mu (N*d) = moebius_mu N * moebius_mu d"
        using mult_moebius unfolding multiplicative_function_def 
        by (simp add: moebius_mu.mult_coprime)
      from a have 2: "h (N*d) = h N * h d"
         using assms(5) unfolding multiplicative_function_def 
         by (simp add: assms(5) multiplicative_function.mult_coprime)
      show "f (a div d) * moebius_mu (N * d) * h (N * d) =
         moebius_mu N * h N * f (a div d) * moebius_mu d * h d"
       by(simp add: divide_simps 1 2)
    qed
    also have "... = (\<Sum> d | d dvd a \<and> coprime N d. moebius_mu N * h N * (f a div f d) * moebius_mu d * h d)"
     apply(rule sum.cong,simp,simp) (*fix this*)
     using multipl_div_mono[of f _ a] assms(4,6-8) 3 by force
    also have "... = moebius_mu N * h N * f a * (\<Sum> d | d dvd a \<and> coprime N d. moebius_mu d * (h d div f d))"
      by(simp add: sum_distrib_left algebra_simps)
    finally show ?thesis by blast
  qed
  also have "... =
           moebius_mu N * h N * f a * (\<Prod>p\<in>{p. p \<in> prime_factors a \<and> \<not> (p dvd N)}. 1 - (h p div f p))"
   proof -
     have "multiplicative_function (\<lambda> d. h d div f d)" 
       using multiplicative_function_divide 
             comp_to_mult 
             assms(4,5) by blast
     then have "(\<Sum>d | d dvd a \<and> coprime N d. moebius_mu d * (h d div f d)) =
    (\<Prod>p\<in>{p. p \<in> prime_factors a \<and> \<not> (p dvd N)}. 1 - (h p div f p))"
       using sum_divisors_moebius_mu_times_multiplicative_revisited[
         of "(\<lambda> d. h d div f d)" a N]         
           assms(8) Ngr0 3 by blast 
    then show ?thesis by argo
  qed    
  also have "... = f(a) * moebius_mu(N) * h(N) * 
     ((\<Prod>p\<in>{p. p \<in> prime_factors (a*N)}. 1 - (h p div f p)) div
     (\<Prod>p\<in>{p. p \<in> prime_factors N}. 1 - (h p div f p)))"
  proof -
    have "{p. p \<in>prime_factors a \<and> \<not> p dvd N} = 
          ({p. p \<in>prime_factors (a*N)} - {p. p \<in>prime_factors N})"
      using p_div_set[of a N] by blast

    then have "(\<Prod>p\<in>{p. p \<in>prime_factors a \<and> \<not> p dvd N}. 1 - h p / f p) = 
          prod (\<lambda> p. 1 - h p / f p) ({p. p \<in>prime_factors (a*N)} - {p. p \<in>prime_factors N})"
      by auto
    also have "... = prod (\<lambda> p. 1 - h p / f p) {p. p \<in>prime_factors (a*N)} div
                     prod (\<lambda> p. 1 - h p / f p) {p. p \<in>prime_factors N}"
      by(intro prod_div_sub)
        (simp,metis "2" Collect_mono N_def a_def dvd_triv_left in_diffD prime_factorization_divide,
         simp,metis assms(6) in_prime_factors_iff)     
    also have "... = (\<Prod>p\<in>{p. p \<in> prime_factors (a*N)}. 1 - (h p div f p)) div
     (\<Prod>p\<in>{p. p \<in> prime_factors N}. 1 - (h p div f p))" by blast
    finally have "(\<Prod>p\<in>{p. p \<in>prime_factors a \<and> \<not> p dvd N}. 1 - h p / f p) = 
        (\<Prod>p\<in>{p. p \<in> prime_factors (a*N)}. 1 - (h p div f p)) div
     (\<Prod>p\<in>{p. p \<in> prime_factors N}. 1 - (h p div f p))" 
      using \<open>(\<Prod>p\<in>{p. p \<in># prime_factorization (a * N)} - {p. p \<in># prime_factorization N}. 1 - h p / f p) = (\<Prod>p\<in>{p. p \<in># prime_factorization (a * N)}. 1 - h p / f p) / (\<Prod>p\<in>{p. p \<in># prime_factorization N}. 1 - h p / f p)\<close> \<open>(\<Prod>p\<in>{p. p \<in># prime_factorization a \<and> \<not> p dvd N}. 1 - h p / f p) = (\<Prod>p\<in>{p. p \<in># prime_factorization (a * N)} - {p. p \<in># prime_factorization N}. 1 - h p / f p)\<close> by auto
      (* fix this : equation should be chained correctly *)
    then show ?thesis by simp
  qed
  also have "... = f(a) * moebius_mu(N) * h(N) * (F(k) div f(k)) * (f(N) div F(N))"
   (is "?a = ?b")
  proof -
    have "F(N) = (f N) *(\<Prod>p\<in> prime_factors N. 1 - (h p div f p))"
      unfolding F_def g_def
      by(intro F_form)(auto simp add: Ngr0 assms(4-6))
    then have eq_1: "(\<Prod>p\<in> prime_factors N. 1 - (h p div f p)) = 
               F N div f N" using 2 f_N_not_z by simp
    have "F(k) = (f k) * (\<Prod>p\<in> prime_factors k. 1 - (h p div f p))"
      unfolding F_def g_def
      by(intro F_form)(auto simp add: assms(4-7))
    then have eq_2: "(\<Prod>p\<in> prime_factors k. 1 - (h p div f p)) = 
               F k div f k" using 2 f_k_not_z by simp

    have "?a = f a * moebius_mu N * h N * 
           ((\<Prod>p\<in> prime_factors k. 1 - (h p div f p)) div
           (\<Prod>p\<in> prime_factors N. 1 - (h p div f p)))"
      using 2 by(simp add: algebra_simps) 
    also have  "... = f a * moebius_mu N * h N * ((F k div f k) div (F N div f N))"
      by(simp add: eq_1 eq_2)
    finally show ?thesis by simp
  qed
  also have "... = moebius_mu N * h N * ((F k * f a * f N) div (F N * f k))"
    by(simp add: algebra_simps) 
  also have "... = moebius_mu N * h N * ((F k * f(a*N)) div (F N * f k))"
  proof -
    have "f a * f N = f (a*N)" 
    proof(cases "a = 1 \<or> N = 1")
      case True
      then show ?thesis  
        using assms(4) completely_multiplicative_function_def[of f] 
        by auto
    next
      case False
      then show ?thesis 
        using 2 assms(4) completely_multiplicative_function_def[of f] 
             Ngr0 3 by auto
    qed
    then show ?thesis by simp
  qed 
  also have "... = moebius_mu N * h N * ((F k * f(k)) div (F N * f k))"
    using 2 by blast
  also have "... = g(N) * (F k div F N)"
    using f_k_not_z g_def by simp
  also have "... = (F(k)*g(N)) div (F(N))" by auto
  finally show ?thesis by simp
qed

(* assumes are necessary to avoid unrolling of 
   the definitions in the theorem *)
theorem s_k_n_dirichlet_expr_abstr:
  fixes f h :: "nat \<Rightarrow> complex" and n k :: nat
  assumes "g = (\<lambda> k. moebius_mu k * h k)" 
  assumes "F = dirichlet_prod f g"
  assumes "N = k div gcd n k" 
  assumes "completely_multiplicative_function f" 
          "multiplicative_function h" 
  assumes "\<And> p. prime p \<Longrightarrow> f(p) \<noteq> 0 \<and> f(p) \<noteq> h(p)" 
  assumes "k > 0" "n > 0"  
  shows "s f g k n = (F(k)*g(N)) div (F(N))"
  using s_k_n_dirichlet_expr assms by blast

(*TODO remove this and substitute 
 the theorem totient_conv_moebius_mu in More_totient by 
 this version: int \<rightarrow> of_nat*)
lemma totient_conv_moebius_mu_of_nat:
  "of_nat (totient n) = dirichlet_prod moebius_mu of_nat n"
proof (cases "n = 0")
  case False
  show ?thesis
    by (rule moebius_inversion)
       (insert False, simp_all add: of_nat_sum [symmetric] totient_divisor_sum del: of_nat_sum)
qed simp_all

corollary c_k_n_dirichlet_expr:
 fixes k n :: nat
 assumes "k > 0" "n > 0" 
 shows "c k n = of_nat (totient k) * 
                moebius_mu (k div gcd n k) div 
                of_nat (totient (k div gcd n k))" 
proof -
  define f :: "nat \<Rightarrow> complex" 
    where "f \<equiv> id"
  define F :: "nat \<Rightarrow> complex"
    where "F \<equiv> (\<lambda> d. dirichlet_prod f moebius_mu d)"
  define g :: "nat \<Rightarrow> complex "
    where "g \<equiv> (\<lambda> l. moebius_mu l)" 
  define N where "N \<equiv> k div gcd n k" 
  define h :: "nat \<Rightarrow> complex"
    where "h \<equiv> (\<lambda> x. (if x = 0 then 0 else 1))" 
  
  have F_is_totient_k: "F k = totient k"
    by(simp add: F_def f_def dirichlet_prod_commutes totient_conv_moebius_mu_of_nat[of k])
  have F_is_totient_N: "F N = totient N"
    by(simp add: F_def f_def dirichlet_prod_commutes totient_conv_moebius_mu_of_nat[of N])

  have "c k n = s id moebius_mu k n"
    using c_k_s_form assms by blast
  also have "... =  s f g k n" 
    unfolding f_def g_def by auto
  also have "... = F k * g N / F N" 
    apply(intro s_k_n_dirichlet_expr_abstr[of _ h])
    unfolding h_def g_def apply(subst fun_eq_iff,simp)   
    by(auto simp add: f_def F_def N_def 
          multiplicative_function_def mult_of_nat_c assms)
  also have "... = of_nat (totient k) * 
                moebius_mu (k div gcd n k) div 
                of_nat (totient (k div gcd n k))"
    by(subst F_is_totient_k, subst F_is_totient_N)(simp add: N_def g_def)
  finally show ?thesis .
qed

section\<open>Gauss sums\<close>



bundle no_vec_lambda_notation
begin
no_notation vec_lambda (binder "\<chi>" 10)
end

subsection\<open>Basic notions\<close>
context
  includes no_vec_lambda_notation
  fixes \<chi> k
  assumes is_char: "\<chi> \<in> dcharacters k"
begin                            

lemma chi_dcharacter: "dcharacter k \<chi>" 
  using is_char unfolding dcharacters_def by simp

(*
 Observe that the case k = 1 corresponds to the trivial
 character (\<lambda> x . 1) which is not of interest here.
*)
lemma mod_positive: "k > 1" 
  using chi_dcharacter 
  unfolding dcharacter_def residues_nat_def by simp

(* TODO remove when integrating periodic and periodic_function *)
lemma dir_periodic: "periodic \<chi> k"
  unfolding periodic_def 
  using is_char dcharacters_def
  by (simp add: dcharacter.periodic)

definition "gauss_sum n = (\<Sum> m = 1..k . \<chi>(m) * unity_root k (m*n))"

lemma ramanujan_to_gauss:
  assumes "\<chi> = principal_dchar k"  
  shows "gauss_sum n = c k n" 
proof -
  {fix m
  from assms  
    have 1: "coprime m k \<Longrightarrow> \<chi>(m) = 1" and
         2: "\<not> coprime m k \<Longrightarrow> \<chi>(m) = 0"  
      unfolding principal_dchar_def by auto}
  note eq = this
  have "gauss_sum n = (\<Sum> m = 1..k . \<chi>(m) * unity_root k (m*n))"
    unfolding gauss_sum_def by simp
  also have "... = (\<Sum> m | m \<in> {1..k} \<and> coprime m k . \<chi>(m) * unity_root k (m*n))"
    by(rule sum.mono_neutral_right,simp,blast,simp add: eq) 
  also have "... = (\<Sum> m | m \<in> {1..k} \<and> coprime m k . unity_root k (m*n))"
    by(simp add: eq)
  also have "... = c k n" unfolding ramanujan_def by blast
  finally show ?thesis .
qed

lemma cnj_chi_n:
  assumes "coprime n k"
  shows "cnj (\<chi> n) * \<chi> n = 1"
proof -
  have "cnj (\<chi> n) * \<chi> n = cmod (\<chi> n)^2"
    by (simp add: mult.commute complex_mult_cnj cmod_def)
  also have "... = 1" 
    using dcharacter.norm[of k \<chi> n]  is_char 
          assms dcharacters_def[of k] by simp
  finally show ?thesis .
qed

(* theorem 8.9 *)
lemma gauss_reduction:
  assumes "coprime n k" 
  shows "gauss_sum n = cnj (\<chi> n) * gauss_sum 1"
proof -  
  have k_gr_0: "k > 0" using mod_positive by simp
  have "gauss_sum n = (\<Sum> r = 1..k . \<chi>(r) * unity_root k (r*n))"
    unfolding gauss_sum_def by simp
  also have "... = (\<Sum> r = 1..k . cnj (\<chi>(n)) * \<chi> n * \<chi> r * unity_root k (r*n))"
    by(rule sum.cong,simp,subst cnj_chi_n,auto simp add: assms)
  also have "... = (\<Sum> r = 1..k . cnj (\<chi>(n)) * \<chi> (n*r) * unity_root k (r*n))"
    apply(rule sum.cong,simp)   
    using is_char by(simp add: dcharacters_def dcharacter.mult)
  also have "... = cnj (\<chi>(n)) * (\<Sum> r = 1..k . \<chi> (n*r) * unity_root k (r*n))"
    by(simp add: sum_distrib_left algebra_simps)
  also have "...= cnj (\<chi>(n)) * (\<Sum> r = 1..k . \<chi> (r)* unity_root k (r))"
  proof -
    have 1: "periodic (\<lambda> r. \<chi> (r)* unity_root k r) k" 
      using dir_periodic unity_periodic mult_periodic by blast
    have "(\<Sum> r = 1..k . \<chi> (n*r) * unity_root k (r*n)) = 
          (\<Sum> r = 1..k . \<chi> (r)* unity_root k (r))"
      using periodic_remove_homothecy[OF assms(1) 1 k_gr_0]
      by(simp add: algebra_simps k_gr_0)
    then show ?thesis by argo
  qed
  also have "... = cnj (\<chi>(n)) * gauss_sum 1" 
    using gauss_sum_def by simp
  finally show ?thesis .
qed

definition "separable n = (gauss_sum n = cnj (\<chi> n) * gauss_sum 1)"

corollary gauss_coprime_separable:
  assumes "coprime n k" 
  shows "separable n" 
  using gauss_reduction[OF assms] unfolding separable_def by simp



(* theorem 8.10 *)
lemma global_separability_condition:
  "(\<forall> n. separable n) \<longleftrightarrow> (\<forall> n. \<not> coprime n k \<longrightarrow> gauss_sum n = 0)"
proof -
  {fix n 
  assume "\<not> coprime n k"
  then have "\<chi>(n) = 0"
    using is_char dcharacters_def 
    using dcharacter.eq_zero_iff by blast
  then have "cnj (\<chi> n) = 0" by blast
  then have "separable n \<longleftrightarrow> gauss_sum n = 0" 
    unfolding separable_def by auto} note not_case = this
  show ?thesis 
    using gauss_coprime_separable 
          not_case separable_def by blast      
qed

corollary principal_not_totally_separable:
  assumes "\<chi> = principal_dchar k"
  shows "\<not> (\<forall> n > 0. separable n)"
proof -
  have k_gr_0: "k > 0" using mod_positive by auto
   

  have tot_0: "totient k \<noteq> 0" by (simp add: k_gr_0)
  have moeb_0: "\<exists> n. moebius_mu (k div gcd n k) \<noteq> 0" 
    by (metis div_self gcd_nat.idem k_gr_0 moebius_mu.one zero_less_iff_neq_zero zero_neq_one)
  
  {fix n :: nat
  assume as: "n > 0"
  have "gauss_sum n = c k n"
    using ramanujan_to_gauss[OF assms(1)] .  
  also have "... = 
   (totient k) * moebius_mu (k div gcd n k) /
     (totient (k div gcd n k))"
    using c_k_n_dirichlet_expr[OF k_gr_0 as] 
    by (metis (no_types, lifting) of_int_moebius_mu of_int_mult of_int_of_nat_eq of_real_divide of_real_of_int_eq)
  finally have "gauss_sum n = 
    (totient k) * moebius_mu (k div gcd n k) /
     (totient (k div gcd n k))" by blast}
  note lem = this
  have 1: "k > 0" using k_gr_0 by simp
  have 2: "\<not> coprime k k" using k_gr_0 using mod_positive by auto
  have 3: "gauss_sum k \<noteq> 0" 
    using lem[of k, OF k_gr_0] tot_0 moebius_mu_1 by simp
  from 1 2 3 have
    "\<exists> n. n > 0 \<and> \<not> coprime n k \<and> gauss_sum n \<noteq> 0" by blast
  then obtain n where "n > 0 \<and> \<not> coprime n k \<and> gauss_sum n \<noteq> 0" by blast

  note right_not_zero = this
  {fix n
  assume "\<not> coprime n k" 
  then have "\<chi>(n) = 0" 
    using assms principal_dchar_def by simp
  then have "cnj (\<chi>(n)) = 0" by blast
  then have "cnj (\<chi>(n)) * gauss_sum 1 = 0" by simp 
  }
  note left_not_zero = this
  then show ?thesis 
     unfolding separable_def 
     using right_not_zero by auto
qed

(* theorem 8.11 *)
theorem gauss_sum_1_mod_square_eq_k: 
  assumes "(\<forall> n. n > 0 \<longrightarrow> separable n)" "k > 0" 
  shows "(cmod (gauss_sum 1))^2 = k" 
proof -
  have "(cmod (gauss_sum 1))^2 = gauss_sum 1 * cnj(gauss_sum 1)"
    using complex_norm_square by blast
  also have "... = gauss_sum 1 * (\<Sum> m = 1..k. cnj (\<chi>(m)) * unity_root k (-m))"
  proof -
    have "cnj (gauss_sum 1) = (\<Sum> m = 1..k. cnj (\<chi>(m)) * unity_root k (-m))"
      unfolding gauss_sum_def by(simp add: unity_cnj)
    then show ?thesis by argo
  qed
  also have "... = (\<Sum> m = 1..k. gauss_sum 1 * cnj (\<chi>(m)) * unity_root k (-m))"
    by(subst sum_distrib_left)(simp add: algebra_simps)
  also have "... = (\<Sum> m = 1..k. gauss_sum m * unity_root k (-m))"
  proof(rule sum.cong,simp)   
    fix x
    assume as: "x \<in> {1..k}"
    show "gauss_sum 1 * cnj (\<chi> x) * unity_root k (-x) =
          gauss_sum x * unity_root k (-x)"
      using assms(1) unfolding separable_def 
      apply(rule allE[of _ x]) using as by auto
  qed
  also have "... = (\<Sum> m = 1..k. (\<Sum> r = 1..k. \<chi> r * unity_root k (r*m) * unity_root k (-m)))"
    unfolding gauss_sum_def 
    by(rule sum.cong,simp,rule sum_distrib_right)
  also have "... = (\<Sum> m = 1..k. (\<Sum> r = 1..k. \<chi> r * unity_root k (m*(r-1)) ))"
  proof(rule sum.cong,simp,rule sum.cong,simp,simp add:  unity_prod )
    fix xa x
    assume "Suc 0 \<le> xa \<and> xa \<le> k"
    then have "int xa * int x - int x = int x * int (xa - Suc 0)"
      by(simp add: algebra_simps,
         metis One_nat_def Suc_diff_le diff_Suc_1 mult_Suc_right of_nat_add of_nat_mult)
    then show "\<chi> xa = 0 \<or> unity_root k (int xa * int x - int x) = unity_root k (int x * int (xa - Suc 0))" by argo
  qed
  also have "... = (\<Sum> r=1..k. (\<Sum> m=1..k.  \<chi>(r) *unity_root k (m*(r-1))))"
    by(rule sum.swap)
  also have "... = (\<Sum> r=1..k. \<chi>(r) *(\<Sum> m=1..k. unity_root k (m*(r-1))))"
    by(rule sum.cong, simp, simp add: sum_distrib_left)
  also have "... = (\<Sum> r=1..k. \<chi>(r) * geometric_sum k (r-1))" 
  proof(rule sum.cong,simp)
    fix x
    assume "x \<in> {1..k}" 
    then have 1: "periodic (\<lambda> m. unity_root k (int (m * (x - 1)))) k" 
      using unity_periodic_mult[of k "x-1"] 
      by(simp add: mult.commute)
    have "(\<Sum>m = 1..k. unity_root k (int (m * (x - 1)))) = 
          (\<Sum>m = 0..k-1. unity_root k (int (m * (x - 1))))"
      using periodic_sum_periodic_shift[OF 1 assms(2), of 1] by simp
    also have "... = geometric_sum k (x-1)"
      unfolding geometric_sum_def 
      by(rule sum.cong,fastforce,simp add: mult.commute)
    finally have "(\<Sum>m = 1..k. unity_root k (int (m * (x - 1)))) =
                  geometric_sum k (int (x - 1))" .
    then show " \<chi> x *
         (\<Sum>m = 1..k. unity_root k (int (m * (x - 1)))) =
         \<chi> x * geometric_sum k (int (x - 1))" by argo
  qed
  also have "... = (\<Sum>r \<in> {1}. \<chi> r * geometric_sum k (int (r - 1)))"    
    apply(rule sum.mono_neutral_right,simp)
    using assms(2) geometric_sum_div int_ops(6) by fastforce+
  also have "... = \<chi> 1 * k" using geo_k_0 assms(2) by simp 
  also have "... = k" using chi_dcharacter dcharacter.Suc_0 by simp
  finally show ?thesis
    by (metis \<open>complex_of_real ((cmod (local.gauss_sum 1))\<^sup>2) = local.gauss_sum 1 * cnj (local.gauss_sum 1)\<close> complex_mod_mult_cnj norm_of_nat)
qed

(*theorem 8.12*)
lemma g_non_zero_when_not_coprime:
  assumes "gauss_sum n \<noteq> 0" "\<not> coprime n k" "n > 0" "k > 0"
  defines "d \<equiv> k div gcd n k"  
  assumes "coprime a k" "[a = 1] (mod d)" 
  shows "d dvd k" "d < k" "\<chi>(a) = 1" 
proof -
  show "d dvd k" 
    unfolding d_def 
    by (metis dvdI dvd_div_mult_self gcd_dvd2)
  from assms(2) have "gcd n k \<noteq> 1" by blast
  then have "gcd n k > 1" using assms(3,4) by (simp add: nat_neq_iff)
  then show "d < k" by (simp add: assms(4) d_def)

  have "periodic (\<lambda> r. \<chi> (r)* unity_root k (n*r)) k" 
    using mult_periodic[OF dir_periodic unity_periodic_mult] by auto
  then have 1: "periodic (\<lambda> r. \<chi> (r)* unity_root k (r*n)) k" 
    by(simp add: algebra_simps)
  
  have "gauss_sum n = (\<Sum> m = 1..k . \<chi>(m) * unity_root k (m*n))"
    unfolding gauss_sum_def by blast
  also have "... = (\<Sum> m = 1..k . \<chi>(m*a) * unity_root k (m*a*n))"
    using periodic_remove_homothecy[OF assms(6) 1 assms(4)] by blast
  also have "... = (\<Sum> m = 1..k . \<chi>(m*a) * unity_root k (m*n))"  
  proof(rule sum.cong,simp)
    fix m
    from assms(7) obtain b where "a = 1 + b*d" 
      using \<open>d < k\<close> assms(6) cong_to_1'_nat by auto
    then have "m*a*n = m*n+m*b*(k div gcd n k)*n" 
      by(simp add: algebra_simps d_def)
    also have "... = m*n+m*b*k*(n div gcd n k)"
      by(simp add: div_mult_swap dvd_div_mult)
    also obtain p where "... = m*n+m*b*k*p" by blast
    finally have "m*a*n = m*n+m*b*k*p" by simp
    then have 1: "m*a*n mod k= m*n mod k" (* fix this *)
      by (metis mod_mult_self1 semiring_normalization_rules(16))
    then have "unity_root k (m * a * n) = unity_root k (m * n)" 
    proof -
      have "unity_root k (m * a * n) = unity_root k ((m * a * n) mod k)"
        using unity_mod[of k] zmod_int by simp
      also have "... = unity_root k (m * n)" 
        using unity_mod[of k] zmod_int 1 by presburger
      finally show ?thesis by blast
    qed
    then show "\<chi> (m * a) * unity_root k (int (m * a * n)) =
               \<chi> (m * a) * unity_root k (int (m * n))" by auto
  qed
  also have "... = (\<Sum> m = 1..k . \<chi>(a) * (\<chi>(m) * unity_root k (m*n)))"
    by(rule sum.cong,simp,subst dcharacter.mult[OF chi_dcharacter],simp)
  also have "... =  \<chi>(a) * (\<Sum> m = 1..k . \<chi>(m) * unity_root k (m*n))"
    using sum_distrib_left[symmetric] (* fix this *)
    by (smt sum.cong vector_space_over_itself.scale_scale)
  also have "... = \<chi>(a) * gauss_sum n" 
    unfolding gauss_sum_def by blast
  finally have "gauss_sum n = \<chi>(a) * gauss_sum n" by blast
  then show "\<chi> a = 1" 
    using assms(1) by simp
qed

subsection\<open>Induced moduli and primitive characters\<close>

definition "induced_modulus d = ((d dvd k) \<and> (\<forall> a. coprime a k \<and> [a = 1] (mod d) \<longrightarrow> \<chi> a = 1))"

lemma zero_not_ind_mod: "\<not> induced_modulus 0" 
  unfolding induced_modulus_def using mod_positive by simp

lemma g_non_zero_ind_mod:
  assumes "gauss_sum n \<noteq> 0" "\<not> coprime n k" "n > 0" "k > 0"
  assumes "d = k div gcd n k"  
  shows  "d < k" "induced_modulus d"
  unfolding induced_modulus_def
  using g_non_zero_when_not_coprime(2)[OF assms(1) 
       assms(2) assms(3) assms(4), of 1, simplified] apply(simp add: assms(5))
  apply(rule conjI)
  using g_non_zero_when_not_coprime(1)[OF assms(1) 
       assms(2) assms(3) assms(4),of 1, simplified] apply(simp add: assms(5))
  apply(safe)
   using g_non_zero_when_not_coprime(3)[OF assms(1) 
       assms(2) assms(3) assms(4)] assms(5) by blast

lemma k_is_ind_mod:
  assumes "k > 0" 
  shows "induced_modulus k" 
  unfolding induced_modulus_def 
proof(rule conjI,simp,safe) 
  fix a 
  assume "[a = 1] (mod k)" 
  then have "a mod k = 1 mod k" 
    using cong_def[of a 1 k] by blast
  also have "... = 1" 
    using chi_dcharacter dcharacter.eq_zero_iff dcharacter.zero_eq_0 by fastforce
  finally have 1: "a mod k = 1" by simp
  
  have "\<chi> a = \<chi> (a mod k)"
    using chi_dcharacter dcharacter.mod by fastforce
  also have "... = \<chi> 1" using cong_def 1 by auto
  also have "... = 1" using chi_dcharacter dcharacter.Suc_0 by simp
  finally show "\<chi> a = 1" by blast
qed

(* theorem 8.13 *)
lemma one_ind_mod_if_pc:
 "induced_modulus 1 \<longleftrightarrow> \<chi> = principal_dchar k"
proof
  assume "induced_modulus 1" 
  then have "(\<forall> a. coprime a k \<longrightarrow> \<chi> a = 1)"
    unfolding induced_modulus_def by simp
  then show "\<chi> = principal_dchar k" 
    unfolding principal_dchar_def 
    using chi_dcharacter dcharacter.eq_zero by auto
next
  assume as: "\<chi> = principal_dchar k"
  {fix a
  assume "coprime a k"
  then have "\<chi> a = 1" 
    using principal_dchar_def as by simp}
  then show "induced_modulus 1"
    unfolding induced_modulus_def by auto
qed

definition "primitive_character = (\<not> (\<exists> d. d < k \<and> induced_modulus d))"

lemma principal_not_primitive_k_gr_1: 
  assumes "k > 1"
  assumes "\<chi> = principal_dchar k" 
  shows "\<not> primitive_character"
  unfolding primitive_character_def
  using one_ind_mod_if_pc assms by blast

(* theorem 8.14 *)
lemma prime_non_principal_is_primitive:
  assumes "prime k"
  assumes "\<chi> \<noteq> principal_dchar k" 
  shows "primitive_character"
proof -
  {fix m
  assume "induced_modulus m" 
  then have "m = k" 
    using assms prime_nat_iff induced_modulus_def
          one_ind_mod_if_pc by blast}
  then show ?thesis using primitive_character_def by blast
qed

(* theorem 8.15 *)
corollary primitive_encoding:
  assumes "primitive_character" "k > 0" 
  shows "\<forall> n. n > 0 \<longrightarrow> gcd n k > 1 \<longrightarrow> gauss_sum n = 0" 
        "\<forall> n. n > 0 \<longrightarrow> separable n"
        "(cmod (gauss_sum 1))^2 = k"
proof(safe)
  {
    fix n :: nat
    assume 1: "n > 0" 
    assume 2: "1 < gcd n k"
    from 1 2 show "gauss_sum n = 0"
      using assms(1) assms(2) 
          g_non_zero_ind_mod(1) g_non_zero_ind_mod(2) 
          primitive_character_def by fastforce}
  note 1 = this
  {fix n :: nat
  assume "n > 0" 
  then show "separable n"
    using global_separability_condition 1
    by (metis chi_dcharacter complex_cnj_zero dcharacter.eq_zero gauss_coprime_separable gcd_eq_0_iff gcd_eq_1_imp_coprime less_one linorder_neqE_nat mult_not_zero neq0_conv separable_def)
  } then show "(cmod (gauss_sum 1))^2 = k"
    using gauss_sum_1_mod_square_eq_k assms(2) by blast
qed

(* theorem 8.16 *)
lemma chi_on_congruent_induced_modulus:
  assumes "d dvd k" "d > 0" 
  shows "induced_modulus d \<longleftrightarrow> (\<forall> a b. coprime a k \<and> coprime b k \<and> [a = b] (mod d) \<longrightarrow> \<chi>(a) = \<chi>(b))"
proof 
  assume 1: "induced_modulus d"
  show "(\<forall> a b. coprime a k \<and> coprime b k \<and> [a = b] (mod d) \<longrightarrow> \<chi>(a) = \<chi>(b))"
  proof(safe)
    fix a b
    assume 2: "coprime a k" "coprime b k" "[a = b] (mod d)"
    show "\<chi>(a) = \<chi>(b)" 
    proof -
      from 2(1) obtain a' where "[a*a' = 1] (mod k)"
        using cong_solve by blast
      from this assms(1) have "[a*a' = 1] (mod d)"
        using cong_dvd_modulus_nat by blast
      from this 1 have "\<chi>(a*a') = 1" 
        unfolding induced_modulus_def 
        by (meson "2"(2) \<open>[a * a' = 1] (mod k)\<close> cong_imp_coprime_nat cong_sym coprime_divisors gcd_nat.refl one_dvd)
      then have 3: "\<chi>(a)*\<chi>(a') = 1" 
        using chi_dcharacter dcharacter.mult by simp

      from 2(3) have "[a*a' = b*a'] (mod d)" by (simp add: cong_scalar_right)
      moreover have 4: "[b*a' = 1] (mod d)" 
        using \<open>[a * a' = 1] (mod d)\<close> calculation cong_sym cong_trans by blast
      from this 1 have "\<chi>(b*a') = 1" 
        unfolding induced_modulus_def 
        by (metis "2"(2) \<open>[a * a' = 1] (mod k)\<close> cong_imp_coprime cong_sym coprime_mult_left_iff mult.right_neutral)
      then have 4: "\<chi>(b)*\<chi>(a') = 1" 
        using chi_dcharacter dcharacter.mult by simp

      from 3 4 show "\<chi>(a) = \<chi>(b)" 
        apply(cases "\<chi>(a') = 0",auto simp add: field_simps)
        using mult_cancel_left by fastforce
    qed
  qed
next 
  assume "\<forall>a b. coprime a k \<and> coprime b k \<and> [a = b] (mod d) \<longrightarrow> \<chi> a = \<chi> b"
  then have "\<forall>a . coprime a k \<and> coprime 1 k \<and> [a = 1] (mod d) \<longrightarrow> \<chi> a = \<chi> 1"
    by blast
  then have "\<forall>a . coprime a k \<and> [a = 1] (mod d) \<longrightarrow> \<chi> a = 1"
    using dcharacter.Suc_0[OF chi_dcharacter] coprime_1_left by simp
  then show "induced_modulus d"
    unfolding induced_modulus_def using assms(1) by blast
qed

(*theorem 8.17*)

(* the case d = 1 is exactly the case 
   described in one_ind_mod_if_pc *)
theorem ind_mod_characterized:
  assumes "d dvd k" "d \<noteq> 1" "k > 0" 
  assumes "\<chi>\<^sub>1 = principal_dchar k" 
  shows "induced_modulus d \<longleftrightarrow> 
         (\<exists> \<Phi>. dcharacter d \<Phi> \<and> (\<forall> n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n))"
proof
  assume as_im: "induced_modulus d" 
  thm technical_m
  define f where
    "f \<equiv> (\<lambda> n. n + 
      (if n = 1 then
         0
       else (prod id {p. prime p \<and> p dvd k \<and> \<not> (p dvd n)})*d)
      )"
  have m_1: "f 1 = 1" unfolding f_def by simp
  {fix n
  assume as: "coprime n d" 
  have "[f n = n] (mod d)" "coprime (f n) k" 
    using technical_m[of k n d "f n" 
      "(\<Prod> p | prime p \<and> p dvd k \<and> \<not> (p dvd n). p)",
       OF assms(3) as] by(auto simp add: f_def)
  }
  note m_prop = this
  
  define \<Phi> where
   "\<Phi> \<equiv> (\<lambda> n. (if \<not> coprime n d then 0 else \<chi>(f n)))"

  have \<Phi>_1: "\<Phi> 1 = 1" 
    unfolding \<Phi>_def 
  proof(simp)
    from m_1 show "\<chi> (f (Suc 0)) = 1" 
      using dcharacter.Suc_0[OF chi_dcharacter] by simp
  qed

  from assms(1-3) have "d > 0" by auto
  from chi_on_congruent_induced_modulus
          [OF assms(1) \<open>d > 0\<close>] as_im 
      have b: "(\<forall>a b. coprime a k \<and> coprime b k \<and> 
                   [a = b] (mod d) \<longrightarrow> \<chi> a = \<chi> b)" by blast

  have \<Phi>_periodic:  " \<forall>a. \<Phi> (a + d) = \<Phi> a" 
  proof 
    fix a
    have "gcd (a+d) d = gcd a d" by auto
    then have cop: "coprime (a+d) d = coprime a d"  
      using coprime_iff_gcd_eq_1 by presburger
    show "\<Phi> (a + d) = \<Phi> a"
    proof(cases "coprime a d")
      case True
      from True cop have cop_ad: "coprime (a+d) d" by blast      
      have p1: "[f (a+d) = f a] (mod d)" 
        using m_prop(1)[of "a+d", OF cop_ad] 
              m_prop(1)[of "a",OF True] by (simp add: cong_def)
      have p2: "coprime (f (a+d)) k" "coprime (f a) k" 
        using m_prop(2)[of "a+d", OF cop_ad]
              m_prop(2)[of "a", OF True] by blast+ 
      from b p1 p2 have eq: "\<chi> (f (a + d)) = \<chi> (f a)" by blast
      show ?thesis 
        unfolding \<Phi>_def 
        by(subst cop,simp,safe, simp add: eq) 
    next
      case False
      then show ?thesis unfolding \<Phi>_def by(subst cop,simp)
    qed  
  qed

  have \<Phi>_mult: "\<forall>a b. a \<in> totatives d \<longrightarrow>
          b \<in> totatives d \<longrightarrow> \<Phi> (a * b) = \<Phi> a * \<Phi> b"
  proof(safe)
    fix a b
    assume "a \<in> totatives d" "b \<in> totatives d"  
    consider (ab) "coprime a d \<and> coprime b d" | 
             (a)  "coprime a d \<and> \<not> coprime b d" |
             (b)  "coprime b d \<and> \<not> coprime a d" |
             (n)  "\<not> coprime a d \<and> \<not> coprime b d" by blast
    then show "\<Phi> (a * b) = \<Phi> a * \<Phi> b" 
    proof cases
      case ab 
      then have c_ab: 
        "coprime (a*b) d" "coprime a d" "coprime b d" by simp+ 
      then have p1: "[f (a * b) = a * b] (mod d)" "coprime (f (a * b)) k"
        using m_prop[of "a*b", OF c_ab(1)] by simp+
      moreover have p2: "[f a = a] (mod d)" "coprime (f a) k"
                    "[f b = b] (mod d)" "coprime (f b) k"
        using m_prop[of "a",OF c_ab(2)]
              m_prop[of "b",OF c_ab(3) ] by simp+
      have p1s: "[f (a * b) = (f a) * (f b)] (mod d)"
      proof -
        have "[f (a * b) = a * b] (mod d)"
          using p1(1) by blast
        moreover have "[a * b = f(a) * f(b)] (mod d)" 
          using p2(1) p2(3) by (simp add: cong_mult cong_sym)
        ultimately show ?thesis using cong_trans by blast
      qed
      have p2s: "coprime (f a*f b) k"
        using p2(2) p2(4) by simp
      have "\<chi> (f (a * b)) = \<chi> (f a * f b)" 
        using p1s p2s p1(2) b by blast 
      then show ?thesis 
        unfolding \<Phi>_def 
        using dcharacter.mult[OF chi_dcharacter]
        by(simp add: c_ab)
    next case a then show ?thesis unfolding \<Phi>_def by simp
    next case b then show ?thesis unfolding \<Phi>_def by simp  
    next case n then show ?thesis unfolding \<Phi>_def by simp
    qed 
  qed
  have d_gr_1: "d > 1" using assms(1,2) 
    using \<open>0 < d\<close> by linarith
  show "\<exists>\<Phi>. dcharacter d \<Phi> \<and> (\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n)" 
  proof(standard,rule conjI) 
    show "dcharacter d \<Phi>" 
      unfolding dcharacter_def residues_nat_def dcharacter_axioms_def 
      using d_gr_1 \<Phi>_def f_def \<Phi>_mult \<Phi>_1 \<Phi>_periodic by simp
    show "\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n" 
    proof
      fix n
      show "\<chi> n = \<Phi> n * \<chi>\<^sub>1 n"
      proof(cases "coprime n k")
        case True
        then have "coprime n d" using assms(1) by auto
        then have "\<Phi>(n) = \<chi>(f n)" using \<Phi>_def by simp
        moreover have "[f n = n] (mod d)" 
          using m_prop[OF \<open>coprime n d\<close>] by simp
        moreover have "\<chi>\<^sub>1 n = 1" 
          using assms(4) principal_dchar_def \<open>coprime n k\<close> by auto
        ultimately show "\<chi>(n) = \<Phi>(n) * \<chi>\<^sub>1(n)" 
        proof -
          assume "\<Phi> n = \<chi> (f n)" "[f n = n] (mod d)" "\<chi>\<^sub>1 n = 1"
          then have "\<chi> n = \<chi> (f n)"
            by (metis True \<open>coprime n d\<close> \<open>dcharacter d \<Phi>\<close> \<open>local.induced_modulus d\<close> assms(1) assms(3) chi_dcharacter chi_on_congruent_induced_modulus dcharacter.eq_zero_iff dvd_pos_nat)
          also have "... = \<Phi> n" by (simp add: \<open>\<Phi> n = \<chi> (f n)\<close>)
          also have "... = \<Phi> n * \<chi>\<^sub>1 n" by(simp add: \<open>\<chi>\<^sub>1 n = 1\<close>)
          finally show ?thesis by simp
        qed
      next
        case False
        then have "\<chi> n = 0" "\<chi>\<^sub>1 n = 0"
          using chi_dcharacter dcharacter.eq_zero_iff apply blast 
          using False assms(4) principal_dchar_def by simp       
        then show ?thesis by simp
      qed      
    qed
  qed
next
  assume "(\<exists> \<Phi>. dcharacter d \<Phi> \<and> (\<forall> n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n))"
  then obtain \<Phi> where 1: "dcharacter d \<Phi>" "(\<forall> n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n)" by blast
  show "induced_modulus d"
    unfolding induced_modulus_def    
  proof(rule conjI,fact,safe)
    fix n
    assume 2: "coprime n k" "[n = 1] (mod d)"
    then have "\<chi>\<^sub>1 n = 1" "\<Phi> n = 1" 
    proof(simp add: assms(4) principal_dchar_def)
      have "\<Phi> n = \<Phi> (n mod d)" by(simp add: dcharacter.mod[OF 1(1), of n])
      also have "... = \<Phi> (1 mod d)" using cong_def[of n 1 d] 2(2) by simp
      also have "... = \<Phi> 1" using assms(2) "1"(1) dcharacter.mod by blast
      also have "... = 1" using dcharacter.Suc_0[OF 1(1)] by simp
      finally show "\<Phi> n = 1" by simp
    qed
    then show "\<chi> n = 1" using 1(2) by simp    
  qed
qed

subsection\<open>The conductor of a character\<close>

definition "conductor = Min {d. induced_modulus d}"

lemma conductor_fin: "finite {d. induced_modulus d}"
proof -
  let ?A = "{d. induced_modulus d}" 
  have "?A \<subseteq> {d. d dvd k}" 
    unfolding induced_modulus_def by blast
  moreover have "finite {d. d dvd k}" using mod_positive by simp
  ultimately show "finite ?A" using finite_subset by auto
qed

lemma k_in_conductor: 
  "k \<in> {d. induced_modulus d}"
  using mod_positive k_is_ind_mod by simp

lemma conductor_in_conductor:
 "conductor \<in> {d. induced_modulus d}"
proof -
  have "{d. induced_modulus d} \<noteq> {}" using k_in_conductor by blast
  then show "conductor \<in> {d. induced_modulus d}" 
    using Min_in[OF conductor_fin ] conductor_def by auto
qed

lemma conductor_dvd: "conductor dvd k"
 using conductor_in_conductor unfolding induced_modulus_def by blast

lemma conductor_is_mod: "induced_modulus conductor" 
  using conductor_in_conductor unfolding induced_modulus_def by blast

lemma conductor_gr_0: "conductor > 0"
  unfolding conductor_def using zero_not_ind_mod 
  using conductor_def conductor_is_mod neq0_conv by fastforce

lemma conductor_1_principal: "conductor = 1 \<longleftrightarrow> \<chi> = principal_dchar k" 
proof
  assume "conductor = 1" 
  then have "induced_modulus 1"
    using conductor_in_conductor by auto
  then show "\<chi> = principal_dchar k"
    using one_ind_mod_if_pc by blast
next
  assume "\<chi> = principal_dchar k"
  then have "induced_modulus 1" using one_ind_mod_if_pc by auto
  then show "conductor = 1" 
    by (metis Min_le conductor_def conductor_fin conductor_gr_0 le_neq_implies_less mem_Collect_eq nat_dvd_not_less one_dvd)
qed

lemma primitive_conductor:
  assumes "\<not> primitive_character"
  shows "conductor < k" 
  by (metis  Min_le assms conductor_def conductor_dvd conductor_fin 
            div_greater_zero_iff dvd_div_eq_0_iff le_neq_implies_less 
            mem_Collect_eq not_le not_less_zero primitive_character_def)

end


thm primitive_character_def conductor_def
context 
  includes no_vec_lambda_notation
begin

(* theorem 8.18 *)
theorem primitive_principal_form:
  assumes is_char: "\<chi> \<in> dcharacters k"
  assumes "\<chi>\<^sub>1 = principal_dchar k"
  assumes "\<chi> \<noteq> principal_dchar k"  
  shows "\<exists> \<Phi>. primitive_character \<Phi> (conductor \<chi> k) \<and>
              (\<forall> n. \<chi>(n) = \<Phi>(n) * \<chi>\<^sub>1(n))"
proof -
  have k_gr_0: "k > 0" using mod_positive[OF assms(1)] by simp
  define d where "d = conductor \<chi> k" 
  have "induced_modulus \<chi> k d" 
    unfolding d_def using conductor_is_mod[OF assms(1)] by blast
  then have d_not_1: "d \<noteq> 1" 
    using assms(3) one_ind_mod_if_pc[OF assms(1)] by auto
  from ind_mod_characterized[OF assms(1) _ d_not_1 k_gr_0 assms(2)]
  obtain \<Phi> where \<Phi>_def: "dcharacter d \<Phi> \<and> (\<forall>n. \<chi> n = \<Phi> n * \<chi>\<^sub>1 n)"
    using \<open>induced_modulus \<chi> k d\<close> induced_modulus_def is_char by blast
  have phi_dchars: "\<Phi> \<in> dcharacters d" using \<Phi>_def dcharacters_def by auto
 
  have \<Phi>_prim: "primitive_character \<Phi> d" 
  proof(rule ccontr)
    assume "\<not> primitive_character \<Phi> d"   
    then obtain q where 
      1: "q dvd d \<and> q < d \<and> induced_modulus \<Phi> d q"
      using primitive_character_def
            induced_modulus_def phi_dchars by blast
    then have 2: "induced_modulus \<chi> k q" 
    proof -
      thm induced_modulus_def
      {fix n
      assume mod_1: "[n = 1] (mod q)" 
      assume cop: "coprime n k" 
      have "\<chi>(n) = \<Phi>(n)*\<chi>\<^sub>1(n)" using \<Phi>_def by auto
      also have "... = \<Phi>(n)" 
        using cop by (simp add: assms(2) principal_dchar_def)  
      also have "... = 1" 
          using 1 mod_1 induced_modulus_def[OF phi_dchars,of q] 
                \<open>induced_modulus \<chi> k d\<close> cop induced_modulus_def is_char by auto
      finally have "\<chi>(n) = 1" by blast}

      then show ?thesis 
        using induced_modulus_def "1" 
              \<open>induced_modulus \<chi> k d\<close> is_char by auto
    qed
     
    show "False" 
    proof-
      from 1 have le: "q < d" by simp
      from d_def conductor_def[OF assms(1)]
      have min: "d = Min {d. induced_modulus \<chi> k d}" by blast
      thm assms(1)
      thm Min_le[of "{d. induced_modulus \<chi> k d}" q]
      from min 2 have "d \<le> q" 
        using Min_le[of "{d. induced_modulus \<chi> k d}" q]
        using conductor_fin is_char by blast
      then show "False" using le by simp
    qed
  qed     

  from \<Phi>_def \<Phi>_prim d_def show ?thesis by blast
qed

theorem 
  assumes is_char: "\<chi> \<in> dcharacters k"
  shows "primitive_character \<chi> k \<longleftrightarrow> (\<forall> n. n > 0 \<longrightarrow> separable \<chi> k n)"
proof 
  assume "primitive_character \<chi> k" 
  show "(\<forall> n. n > 0 \<longrightarrow> separable \<chi> k n)" 
    using \<open>primitive_character \<chi> k\<close> mod_positive primitive_encoding(2) is_char
    by blast
next
  assume tot_separable: "\<forall>n>0. separable \<chi> k n" 
  show "primitive_character \<chi> k"
  proof(cases "\<chi> = principal_dchar k")
    case True
    then show ?thesis
      using principal_not_totally_separable[OF assms(1) True]
            tot_separable by blast
  next
    case False
    {assume as: "\<not> primitive_character \<chi> k"
     have "\<exists> r. \<not> coprime r k \<and> gauss_sum \<chi> k r \<noteq> 0"
     proof -
       have "k > 1" using is_char mod_positive by auto
       define d where "d = conductor \<chi> k"
       have "d > 0" unfolding d_def using conductor_gr_0[OF assms(1)] .
       have "d < k" unfolding d_def using primitive_conductor[OF assms(1) as] .
       have "d dvd k" unfolding d_def using conductor_dvd[OF assms(1)] by blast
       define r where "r = k div d"
       have "gcd r k > 1" unfolding r_def 
        by (metis One_nat_def Suc_lessI \<open>1 < k\<close> \<open>d < k\<close> conductor_dvd d_def dvd_mult_div_cancel dvd_triv_right gcd_nat.absorb1 gcd_pos_nat is_char mult.right_neutral nat_neq_iff)
       then have 1: "\<not> coprime r k" by auto
       define \<chi>\<^sub>1 where "\<chi>\<^sub>1 = principal_dchar k" 
       from primitive_principal_form[OF assms(1) \<chi>\<^sub>1_def False]
       obtain \<Phi> where prod: "(\<forall> n. \<chi>(n) = \<Phi>(n)*\<chi>\<^sub>1(n))" by blast

       have "gauss_sum \<chi> k r  = (\<Sum> m = 1..k . \<chi>(m) * unity_root k (m*r))"
         unfolding gauss_sum_def[OF assms(1)] by blast
       also have "... = (\<Sum> m = 1..k . \<Phi>(m)*\<chi>\<^sub>1(m) * unity_root k (m*r))"
         by(rule sum.cong,auto simp add: prod) 
       also have "... = (\<Sum> m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m)*\<chi>\<^sub>1(m) * unity_root k (m*r))"
         apply(rule sum.mono_neutral_right,simp,blast)
         using \<chi>\<^sub>1_def unfolding principal_dchar_def by auto
       also have "... = (\<Sum> m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m)*\<chi>\<^sub>1(m) * unity_root d m)"
       proof(rule sum.cong,simp)
         fix x
         assume "x \<in> {m \<in> {1..k}. coprime m k}" 
         have "k > 0" using \<open>k > 1\<close> by simp
         have "unity_root k (int (x * r)) = unity_root d (int x)"
           using unity_div_num[OF \<open>k > 0\<close> \<open>d > 0\<close> \<open>d dvd k\<close>]
           by(simp add: algebra_simps r_def)
         then show "\<Phi> x * \<chi>\<^sub>1 x * unity_root k (int (x * r)) =
                    \<Phi> x * \<chi>\<^sub>1 x * unity_root d (int x)" by auto
       qed
       also have "... = (\<Sum> m | m \<in> {1..k} \<and> coprime m k. \<Phi>(m) * unity_root d m)"
         by(rule sum.cong,auto simp add: \<chi>\<^sub>1_def principal_dchar_def)
       also have "... = (totient k div totient d) * (\<Sum> m | m \<in> {1..k} \<and> coprime m d. \<Phi>(m) * unity_root d m)"
         
       }
  then show "primitive_character \<chi> k" 
    using gauss_reduction gauss_coprime_separable 
    sorry
    then show ?thesis
      
      sorry
  qed
qed


end


end