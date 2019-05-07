theory Congruences
  imports "HOL-Number_Theory.Number_Theory"
begin

(* theorem 5.32 *)
lemma 
  fixes r d k :: nat
  assumes "d > 0" "k > 0"  "coprime r d"
  shows "card {e . e = r+t*d \<and> t \<in> {1..k div d}} = 
         totient k div totient d"
proof - 
  define S where "S = {e . e = r+t*d \<and> t \<in> {1..k div d}}" 
  {fix p :: nat
  assume 1: "prime p" "p dvd k" "p dvd r+t*d"
  have "\<not> p dvd d"
  proof(rule ccontr,simp)
    assume "p dvd d"
    then have "p dvd r" using 1(3) by (simp add: dvd_add_left_iff)
    then have "\<not> coprime r d" using \<open>p dvd d\<close> 
      using "1"(1) assms(3) coprime_common_divisor_nat prime_nat_iff by auto
    then show "False" using assms(3) by simp
  qed}
  note lem = this
  have "{p. prime p \<and> p dvd k \<and> (\<exists> x \<in> S. p dvd x)} = 
        {p. prime p \<and> p dvd k \<and> \<not> p dvd d}"
   (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B" 
      using S_def lem by blast
    show "?B \<subseteq> ?A" 
    proof -
     

    qed
  qed

end