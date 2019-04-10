(*
Here "defines" gives the error:

Bad head of lhs: existing constant "of_nat"
The error(s) above occurred in definition:
"of_nat (g n) \<equiv>
 \<Sum>m\<le>k - 1.
    exp (complex_of_real
          (real_of_int (int (2 * m) * n) / real k * pi) *
         \<i>)"

*)

lemma case_1:
  fixes n :: int and k :: nat
  assumes gr: "k \<ge> 1"
  assumes dvd: "k dvd n"
  defines  "g(n) == (\<Sum>m\<le>k-1.exp ((2*m*n/ k)*pi*\<i>))"
  shows "g(n) = k"

(* So I come back to the original form *)

lemma case_1:
  fixes n :: int and k :: nat
  assumes gr: "k \<ge> 1"
  assumes dvd: "k dvd n"
  assumes def:  "g(n) = (\<Sum>m\<le>k-1.exp ((2*m*n/ k)*pi*\<i>))"
  shows "g(n) = k"
proof -
  let ?x = "exp ((2*n/k)*pi*\<i>)"
  have unit: "?x = 1" using exp_dvd dvd gr by simp
  have exp: "\<And> m. ?x^m = exp ((2*m*n/ k)*pi*\<i>)"
    by(simp add: algebra_simps,
       metis (no_types, lifting) exp_of_nat_mult semiring_normalization_rules(19) times_divide_eq_left)
  have "g(n) = (\<Sum>m\<le>k-1. ?x^m)" 
    using def exp by simp  
  then have "g(n) = (\<Sum>m\<le>k-1. 1)" 
(* Here I cannot be prove easily with try0 or sledgehammer.
   It does that work with simp if I instead write:
*)
  moreover have "... = (\<Sum>m\<le>k-1. 1)" 
    using unit by simp
(* But the problem comes back if I try to finish with:*)
  ultimately have "g(n) = (\<Sum>m\<le>k-1. 1)" 
(* I cannot easily prove it.
  I think the problem might be that the assumptions are
  written as "of_nat g(n) =..." while the conclusion does
  not have the "of_nat" part. 

  So in summary I think I need some advice in how to deal
  with different types and conversions between types.
*)
