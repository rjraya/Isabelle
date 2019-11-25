(*

(* Delta arithmetic can be used to proof independence of the representant much quicker
   although understanding is similar *)

lemma only_one:
  assumes "(q1,q2) ∈ gluing" "proj_add p q1 ≠ undefined" "proj_add p q2 ≠ undefined"
  shows "(proj_add p q1, proj_add p q2) ∈ gluing"
proof -
  obtain p1 p2 pl q11 q12 ql1 q21 q22 ql2 where p_expr:
    "p = ((p1,p2),pl)"
    "q1 = ((q11,q12),ql1)"
    "q2 = ((q21,q22),ql2)" 
    by (metis surj_pair)

  have in_aff: "(q11,q12) ∈ e'_aff" "(q21,q22) ∈ e'_aff"
    using assms gluing_aff p_expr by blast+

  consider (1) "((q21,q22) = (q11,q12) ∧ ql1 = ql2)" | 
           (2) "((q21,q22) = τ (q11,q12) ∧ ql2 = ql1+1 ∧ q11 ≠ 0 ∧ q12 ≠ 0)"
    using assms gluing_char p_expr(2) p_expr(3) by fastforce
  then show ?thesis
  proof(cases)
    case 1
    then have "q1 = q2"
      using p_expr by auto
    then have "proj_add p q1 = proj_add p q2"
      by simp
    then show ?thesis 
      using eq_rel 
      unfolding e'_aff_bit_def equiv_def refl_on_def
      
      sorry
  next
    case 2
    have e_proj: "gluing `` {((p1, p2), pl)} ∈ e_proj" "gluing `` {((q11, q12), ql1)} ∈ e_proj"
      using assms proj_add.simps(3) e_proj_aff p_expr in_aff by blast+
    have e_proj_tau: "gluing `` {(τ (q11, q12), ql1)} ∈ e_proj"
      using "2" e_proj_aff in_aff(2) by auto
    have "τ (fst (proj_add p q1)) = fst (proj_add p q2)"
      unfolding p_expr 
      using 2
      apply(simp del: τ.simps)
      using covering_with_deltas[OF e_proj] 
            covering_with_deltas[OF e_proj(1), of "fst (τ (q11, q12))" "snd (τ (q11, q12))", 
                                 simplified prod.collapse, OF e_proj_tau,simplified tau_idemp_point]
      apply(safe)
      apply (metis add.simps add_ext_add curve_addition.commutativity e_proj(1) e_proj_aff ext_curve_addition.ext_add_comm_points ext_curve_addition_axioms fst_conv in_aff mix_tau_prime proj_add.simps snd_conv tau_idemp_explicit)
      apply (metis curve_addition.commutativity e_proj(1) e_proj_aff ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(1) in_aff(2) proj_add.simps(1) proj_add.simps(2) snd_conv tau_idemp_point)
            apply (metis add_ext_add add_ext_add_2 assms(3) commutativity ext_curve_addition.ext_add_comm ext_curve_addition_axioms fst_conv in_aff(1) mix_tau_prime p_expr(1) p_expr(3) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_point)
            apply (metis add_ext_add add_ext_add_2 assms(3) curve_addition.commutativity ext_curve_addition.ext_add_comm ext_curve_addition_axioms fst_conv in_aff(1) p_expr(1) p_expr(3) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_point)
            apply (metis add.simps add_ext_add commutativity e_proj(1) e_proj_aff ext_add_comm_points fst_conv in_aff(1) in_aff(2) proj_add.simps(1) proj_add.simps(2) snd_conv tau_idemp_explicit)
            apply (metis add.simps add_ext_add assms(2) commutativity ext_curve_addition.ext_add_comm_points ext_curve_addition.mix_tau_prime ext_curve_addition_axioms fst_conv in_aff(2) p_expr(1) p_expr(2) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_explicit)
            apply (metis assms(2) curve_addition.commutativity ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(2) mix_tau p_expr(1) p_expr(2) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_point)
            apply (metis curve_addition.commutativity e_proj(1) e_proj_aff ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(1) in_aff(2) mix_tau proj_add.simps(1) proj_add.simps(2) snd_conv tau_idemp_point)
            apply (metis add_ext_add add_ext_add_2 assms(3) curve_addition.commutativity ext_curve_addition.ext_add_comm ext_curve_addition_axioms fst_conv in_aff(1) p_expr(1) p_expr(3) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_point)
            apply (smt τ.simps assms(3) curve_addition.commutativity division_ring_divide_zero ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(1) mix_tau mult_zero_right p_expr(1) p_expr(3) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) tau_idemp_explicit)
      apply (metis assms(2) curve_addition.commutativity ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(2) mix_tau p_expr(1) p_expr(2) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_point)
      apply (metis assms(2) curve_addition.commutativity ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(2) mix_tau p_expr(1) p_expr(2) proj_add.simps(1) proj_add.simps(2) proj_add.simps(3) snd_conv tau_idemp_point)
            apply (metis Pair_inject add_ext_add c_eq_1 commutativity e_proj(1) e_proj_aff ext_curve_addition.ext_add_comm ext_curve_addition.mix_tau_prime ext_curve_addition_axioms in_aff(1) in_aff(2) proj_add.simps(1) proj_add.simps(2) surjective_pairing tau_idemp_explicit)
            apply (metis add.simps add_ext_add curve_addition.commutativity e_proj(1) e_proj_aff ext_curve_addition.ext_add_comm ext_curve_addition_axioms fst_conv in_aff(1) in_aff(2) proj_add.simps(1) proj_add.simps(2) snd_conv tau_idemp_explicit)
            apply (metis curve_addition.commutativity e_proj(1) e_proj_aff ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(1) in_aff(2) proj_add.simps(1) proj_add.simps(2) snd_conv tau_idemp_point)
            by (metis curve_addition.commutativity e_proj(1) e_proj_aff ext_add_comm ext_curve_addition.add_ext_add_2 ext_curve_addition_axioms fst_conv in_aff(1) in_aff(2) mix_tau proj_add.simps(1) proj_add.simps(2) snd_conv tau_idemp_point)
    then show ?thesis 
      
      sorry
  qed
qed

lemma only_one_2:
  assumes "(p1,p2) ∈ gluing" "(q1,q2) ∈ gluing" 
          "proj_add p1 q1 ≠ undefined" "proj_add p1 q2 ≠ undefined"
          "proj_add p2 q1 ≠ undefined" "proj_add p2 q2 ≠ undefined"
  shows "(proj_add p1 q1, proj_add p2 q2) ∈ gluing"
proof -
  have "(proj_add p1 q1, proj_add p1 q2) ∈ gluing"
    using only_one assms(2) assms(3) assms(4) by blast
  also have "(proj_add p1 q2, proj_add p2 q2) ∈ gluing"
    using only_one assms 
    by (metis prod.collapse proj_add_comm)
  finally show ?thesis
    sorry
qed



lemma gluing_add_2:
  assumes
          "gluing `` {((x,y),l)} ∈ e_proj" "gluing `` {((x',y'),l')} ∈ e_proj" "delta x y x' y' ≠ 0"
        shows "proj_addition (gluing `` {((x,y),l)}) (gluing `` {((x',y'),l')}) = (gluing `` {(add (x,y) (x',y'),l+l')})"
  
proof -
  have class_lemmas: "((x,y),l) ∈ gluing `` {((x, y), l)}" 
                     "((x',y'),l') ∈ gluing `` {((x',y'),l')}"
                     "((x,y),(x',y')) ∈ e'_aff_0" 
                     "proj_add ((x,y),l) ((x',y'),l') = (add (x,y) (x',y'),l+l')"
    using assms(1) gluing_cases_points apply blast
    using assms(2) gluing_cases_points apply blast
    unfolding e'_aff_0_def using assms e_proj_aff by auto

  have "gluing `` {(add (x,y) (x',y'),l+l')} ∈ 
          proj_add_class (gluing `` {((x, y), l)}) (gluing `` {((x', y'), l')})"
    apply(subst proj_add_class.simps(1)[OF assms(1-2)])
    apply(rule quotientI[of _ _ gluing])
    using class_lemmas by force

  {
    fix g
    assume "g ∈ proj_add_class (gluing `` {((x, y), l)}) (gluing `` {((x', y'), l')})"
    then obtain p1 p2 where "g = gluing `` {proj_add p1 p2}" "p1 ∈ gluing `` {((x, y), l)}" "p2 ∈ gluing `` {((x', y'), l')}"
      using proj_add_class.simps(1)[OF assms(1-2)] 
      by (smt mem_Collect_eq quotientE)
    have "fst (proj_add p1 p2) ∈ e'_aff"
    then have "gluing `` {(add (x,y) (x',y'),l+l')} = gluing `` {proj_add p1 p2}"
      using only_one 

  }
  then show ?thesis
    unfolding proj_addition_def 
    
    oops
   
qed

*)
