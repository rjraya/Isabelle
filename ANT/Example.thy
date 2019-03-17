theory Example
  imports Main HOL.Complex "HOL-Algebra.Divisibility" 
          HOL.Series
begin

thm geometric_sum
term exp
thm exp_def
thm norm_ii

term hurwitz_zeta

term "\<Sum>m \<in> {0..k-1}. f m"
term "\<lambda> k. exp ((2* of_real pi*\<i>*m*n)/k)"
term "of_real"

lemma 
  "exp ((2*pi*(n::nat)/(k::nat)) *\<i>) = 1 \<longleftrightarrow> k dvd n"
proof(rule iffI)
  (* e^(ix) = cos x + i sin x *)
  assume "exp ((2*pi*n/k)*\<i>) = 1"
  then have "sin (2*pi*n/k) = 0" 
    by (metis cis.sel(2) cis_conv_exp mult.commute one_complex.simps(2))
  then obtain l where "2*pi*n/k = l*pi"
    using sin_zero_iff_int2 by blast
  then have "2*n/k = l" 
    sledgehammer
  then show "k dvd n" 
    
    sorry
next
  assume "k dvd n"
  show "exp ((2*pi*n*\<i>) / k) = 1"
    sorry
qed

lemma
  assumes 0: "(k::nat) \<ge> 1"
  assumes 1: "k dvd n"
  assumes 2: "g(n::nat) = (\<Sum>m \<in> {0..(k::nat)-1}. exp ((2*pi*m*n*\<i>) / k))"
  shows "g(n) = k"
proof -
  let ?x = "exp ((2*pi*n*\<i>) / k)"
  have "\<And> m. exp ((2*pi*m*n*\<i>) / k) = (?x)^m"
    by (smt exp_of_nat_mult mult_of_nat_commute of_real_mult 
            of_real_of_nat_eq semiring_normalization_rules(16) 
            times_divide_eq_right)
  from this 2 have 3: "g(n) = (\<Sum>m \<in> {0..k-1}. (?x)^m)"
    by simp
  from 1 have "\<exists> (l::nat). ?x = exp (2*pi*l*\<i>)" 
    by (smt of_real_divide of_real_of_nat_eq real_of_nat_div times_divide_eq_left times_divide_eq_right)
  then have "?x = 1" 
    by (metis exp_of_nat2_mult exp_two_pi_i mult.commute of_nat_numeral of_real_mult of_real_of_nat_eq power_one semiring_normalization_rules(19))
  from 3 this have "g(n) = (\<Sum>m \<in> {0..k-1}. 1)" by auto
  then show ?thesis  
      by (metis "0" One_nat_def Suc_pred atLeast0AtMost 
                atLeastAtMost_iff card_atLeastAtMost diff_zero 
                lessThan_Suc_atMost lessThan_iff linorder_not_le 
                mult.right_neutral sum_constant zero_order(1))
qed                       

lemma
  assumes 0: "(k::nat) \<ge> 1"
  assumes 1: "\<not> k dvd n"
  assumes 2: "g(n::nat) = (\<Sum>m \<in> {0..(k::nat)-1}. exp ((2*pi*m*n*\<i>) / k))"
  shows "g(n) = 0"
proof -
  let ?x = "exp ((2*pi*n*\<i>) / k)"
  thm DeMoivre Im_exp[of "(2*pi*n*\<i>) / k"]
  from 0 1 have "Im (2*pi*n*\<i>) / k = (2*pi*n) / k" by fastforce
  from 1 have "\<not> (\<exists> (l::int). (2*pi*n*\<i>) / k = l * pi)"
    sorry
  from 1 have "sin ((2*pi*n) / k) \<noteq> 0"  sorry
  from 1 this have "?x \<noteq> 1" 
    by (metis cis.sel(2) cis_conv_exp of_real_divide 
              of_real_of_nat_eq one_complex.simps(2) semiring_normalization_rules(7) times_divide_eq_left)
  then have 3: "(?x^k - 1)/(?x - 1) = (\<Sum> m \<in> {0..k-1}. ?x^m)"
      using geometric_sum[of ?x k]
      by (metis One_nat_def Suc_pred atLeast0AtMost divide_eq_0_iff 
                exp_zero lessThan_Suc_atMost neq0_conv of_nat_eq_0_iff)
  then have "\<And> m. exp ((2*pi*m*n*\<i>) / k) = (?x)^m"
    by (smt exp_of_nat_mult mult_of_nat_commute of_real_mult 
            of_real_of_nat_eq semiring_normalization_rules(16) 
            times_divide_eq_right)
  from this 2 3 have 4: "g(n) = (?x^k - 1)/(?x - 1)"
    by simp
  from 0 have "?x^k = exp (2*pi*n*\<i>)"
    using exp_divide_power_eq linorder_not_le by blast
  then have "?x^k = 1" 
    by (metis exp_of_nat2_mult exp_two_pi_i' mult.commute of_nat_numeral
              of_real_mult of_real_of_nat_eq power_one semiring_normalization_rules(19))
  from this 4 show ?thesis by auto
qed

end