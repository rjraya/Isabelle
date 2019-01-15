
structure Dch_tc = struct val thy = theory "Dch_tc" end ;
val _ = use_legacy_bindings Dch_tc.thy ;

val _ = qed_goal "tc2ch_unit" Dch_tc.thy 
  "tc2ch o unit_tc = unitU" 
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [unitU_def]) 1) ]) ;

val _ = qed_goal "tc2ch_mm" Dch_tc.thy 
  "tc2ch o ext_tc f = extU (tc2ch o f) o tc2ch"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [extU_alt]) 1),
    (case_tac "x" 1), Safe_tac, 
    (simp_tac (esimps [uca_ext.eq_norm, uc_ext_UN]) 1),
    (simp_tac (esimps [uca_ext.eq_norm, uc_ext_UN, uc_pext_Un_uc_of]) 1),
    (res_inst_tac [("A", "f ` s")] oset_cases 1),

    (asm_simp_tac (esimps [uc_pext_def]) 2),
    cong_tac 2, (dtac ([equalityD2, insertI1] MRS subsetD) 2),
    Safe_tac, (datac bspec 1 2), (dtac sym 2),
    (clarsimp_tac (cesimps [uca_ext.eq_norm]) 2),

    (clarsimp_tac (cesimps [uc_pext_alt, image_compose,
      uca_ext.norm_eq_iff RS sym]) 1), 
    (* get rid of tc2ch, get goal in terms of uc_xxx only *)
    (simp_tac (esimps [uc_prod_def, uc_swap_def, uca_ext.eq_norm]) 1),
    (simp_tac (esimps [symmetric uc_kmap_def, mk_sap uc_ax8Kmj]) 1), 
    (rtac tc_mm_lem' 1) ]) ;

val tc2ch_mm' = mk_ap tc2ch_mm ;

(* alternative proof that tc is a monad, uses that tc2ch is injective *)
val _ = qed_goal_spec_mp "tc2ch_inj" Dch_tc.thy 
  "tc2ch A = tc2ch B --> A = B"
  (fn _ => [ (case_tac "A" 1), (ALLGOALS (case_tac "B")), 
    (auto_tac (cesimps [uca_ext.norm_eq_iff RS sym])) ]) ;

val _ = qed_goal_spec_mp "tc2ch_o_inj" Dch_tc.thy 
  "tc2ch o A = tc2ch o B --> A = B"
  (fn _ => [ (rtac impI 1), (rtac ext 1), 
    (dtac fun_cong 1), (Full_simp_tac 1), (etac tc2ch_inj 1) ]) ;

(* note - avoid using default simplification as contains E1/2 for tc *)
val _ = qed_goal "tc2ch_E1" Dch_tc.thy "ext_tc f o unit_tc = f"
  (fn _ => [ (rtac tc2ch_o_inj 1),
    (simp_tac (HOL_ss addsimps 
      [o_assoc, tc2ch_mm, mk_oap tc2ch_unit, E1]) 1) ]) ;

val _ = qed_goal "tc2ch_E2" Dch_tc.thy "ext_tc unit_tc = id"
  (fn _ => [ (rtac tc2ch_o_inj 1), 
    (simp_tac (HOL_ss addsimps [tc2ch_mm, tc2ch_unit, E2, o_id, id_o]) 1) ]) ;
    
val _ = qed_goal "tc2ch_E3'" Dch_tc.thy 
  "ext_tc (ext_tc B o A) = ext_tc B o ext_tc A"
  (fn _ => [ (rtac tc2ch_o_inj 1),
    (simp_tac (HOL_ss addsimps [o_assoc, tc2ch_mm]) 1),
    (simp_tac (HOL_ss addsimps [o_assoc RS sym, tc2ch_mm, E3']) 1) ]) ;

