
structure Dch = struct val thy = theory "Dch" end ;
val _ = use_legacy_bindings Dch.thy ;

val seq_ch_def' = prove_goal Dch.thy "seq_ch A B == extU B o A"
  (fn _ => [ (rtac meta_ext 1), (simp_tac (esimps [seq_ch_def]) 1) ]) ;

val _ = qed_goalw "wp_ch_alt" Dch.thy [wp_ch_def, uc_eval_def]
  "wp_ch A P s == uc_eval (Rep_uca (A s)) P" fn_at ;

val _ = qed_goal "All_uc_lem" Chorus.thy
  "(ALL Y:uc_of S. X <= Y) = (ALL Y:S. X <= Y)"
  (fn _ => [ Safe_tac, (dtac bspec 1), (etac uc_inI 1), Auto_tac ]) ;

val _ = qed_goal "Ex_uc_lem" Chorus.thy
  "(EX Y:uc_of S. Y <= X) = (EX Y:S. Y <= X)"
  (fn _ => [ Safe_tac, (etac rev_bexI 1), (etac bexI 2), Auto_tac ]) ;

val _ = qed_goalw "wp_ch_unitU" Dch.thy [wp_ch_def, unitU_def]
  "wp_ch (%s. unitU (f s)) P x = P (f x)"
  (fn _ => [ (simp_tac (esimps [uca_ext.eq_norm, Ex_uc_lem]) 1) ]) ;

val _ = qed_goalw_spec_mp "wp_ch_li_mono" Dch.thy [liftimp, wp_ch_def]
  "(P ---> Q) --> (wp_ch A P ---> wp_ch A Q)"
  (fn _ => [ (strip_tac 1), (etac bex_match 1), Fast_tac 1 ]) ;

val wp_ch_mono = (rewrite_rule [liftimp] wp_ch_li_mono RS spec) ;
val wp_ch_mono' = rotate_prems ~1 (wp_ch_mono RS mp) ;

val _ = qed_goal "wp_ch_evalU" Dch.thy 
  "wp_ch A Q == C_ evalU Q o A" 
  (fn _ => [ (rtac meta_ext 1),
    (simp_tac (esimps [evalU_def', wp_ch_def, C_def]) 1) ]) ;
  
val _ = qed_goalw "wp_ch_seq" Dch.thy [wp_ch_evalU, seq_ch_def']
  "wp_ch (seq_ch A B) P = wp_ch A (wp_ch B P)"
  (fn _ => [ (simp_tac (esimps [o_assoc, evalU_extU]) 1) ]) ;
  
(* older proof
val _ = qed_goal "wp_ch_seq" Dch.thy
  "wp_ch (seq_ch A B) P = wp_ch A (wp_ch B P)"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [wp_ch_def, seq_ch_def, extU_alt,
      uca_ext.eq_norm, in_Collect]) 1),
    Safe_tac, (dtac (uc_ext_alt RS iffD1) 1), Full_simp_tac 1,
    (REPEAT (eresolve_tac [bex_match, ball_match] 1)), Fast_tac 1,
    (rtac bexI 1), (rtac (uc_ext_alt RS iffD2) 2), Simp_tac 2, 
    (REPEAT (eresolve_tac [rev_bexI, bex_match, ball_match] 2)), 
    (rtac ([in_Collect, subset_refl] MRS iffD1) 1), Auto_tac ]) ;
*)

val _ = qed_goal "seq_ch_assoc" Dch.thy
  "seq_ch A (seq_ch B C) = seq_ch (seq_ch A B) C"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [seq_ch_def, mk_ap E3' RS sym]) 1),
    cong_tac 1, (rtac ext 1), (simp_tac (esimps [seq_ch_def]) 1) ]) ;

val _ = qed_goalw_spec_mp "wp_ch_inj" Dch.thy [wp_ch_def]
  "wp_ch A = wp_ch B --> A = B"
  (fn _ => [ Safe_tac, (rtac ext 1), (rtac uca_ext.Rep_eqD 1), Safe_tac, 
    (REPEAT (EVERY [(dres_inst_tac [("x", "%x. x : xa")] fun_cong 1),
      (dtac fun_cong 1), (full_simp_tac (esimps [wp_ch_def]) 1),
      (dresolve_tac [iffD1, iffD2] 1 THEN etac rev_bexI 1),
      (rtac order_refl 1), Clarify_tac 1,
      (datac uc_of.I 1 1), Full_simp_tac 1])) ]) ; 

val wp_ch_inj_ext = ext RS (ext RS wp_ch_inj) ;

(* seq_ch_assoc, alternative proof *)
val _ = qed_goal "seq_ch_assoc" Dch.thy
  "seq_ch A (seq_ch B C) = seq_ch (seq_ch A B) C"
  (fn _ => [ (rtac wp_ch_inj_ext 1), (simp_tac (esimps [wp_ch_seq]) 1) ]) ;

(* alternative (and easier!) proof of monad structure *)
val E3'_alt = simplify (esimps [seq_ch_def'])
  (read_instantiate [("A", "id")] seq_ch_assoc) ;

val _ = qed_goalw_spec_mp "ref_ch_antisym" Dch.thy [ref_ch_def, liftimp]
  "ref_ch A B --> ref_ch B A --> A = B"
  (fn _ => [ Safe_tac, (rtac wp_ch_inj 1), 
    (rtac ext 1), (rtac ext 1), Fast_tac 1 ]) ;
    
val _ = qed_goalw "fis_ch_alt" Dch.thy [o_def]
  "fis_ch A == Not o wp_ch A (%x. False)"
  (fn _ => [ (rtac meta_ext 1),
    (auto_tac (cesimps [fis_ch_def, wp_ch_def])) ]) ;

val _ = qed_goal "trm_ch_alt" Dch.thy 
  "trm_ch A == wp_ch A (%x. True)"
  (fn _ => [ (rtac meta_ext 1),
    (auto_tac (cesimps [trm_ch_def, wp_ch_def])) ]) ;

val _ = qed_goalw "wp_ch_magic" Dch.thy [wp_ch_def, magic_ch_def]
  "wp_ch magic_ch P s"
  (fn _ => [ (auto_tac (cesimps [uca_ext.eq_norm])) ]) ;
  
val _ = qed_goalw "wp_ch_abort" Dch.thy [wp_ch_def, abort_ch_def]
  "~ wp_ch abort_ch P s"
  (fn _ => [ (clarsimp_tac (cesimps [uca_ext.eq_norm]) 1) ]) ;
  
val _ = qed_goal "wp_conjugate" Dch.thy 
  "wp_ch (conjugate A) P == Not o wp_ch A (Not o P)"
  (fn _ => [ (rtac meta_ext 1),
    (simp_tac (esimps [wp_ch_def, conjugate_def, uca_ext.eq_norm]) 1), 
    (simp_tac (esimps [uc_swap_def]) 1), 
    Safe_tac, (datac bspec 1 1), (etac intneE 1), Force_tac 1,
    (rtac exI 1), (rtac conjI 1), (rtac order_refl 2),
    (etac ball_match 1), Force_tac 1 ]) ;

val _ = qed_goal "conjugate_unitU" Dch.thy 
  "conjugate (unitU o f) = unitU o f"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_conjugate, o_def, wp_ch_unitU]) 1) ]) ;

val _ = qed_goalw "wp_ch_ang" Dch.thy [wp_ch_def, ang_ch_def]
  "wp_ch (ang_ch As) P s = (EX A:As. wp_ch A P s)"
  (fn _ => [ (simp_tac (esimps [uca_ext.eq_norm, UN_im_uc_of RS sym]) 1) ]) ;

val _ = qed_goalw "wp_ch_dem" Dch.thy [wp_ch_def, dem_ch_def]
  "wp_ch (dem_ch As) P s = (ALL A:As. wp_ch A P s)"
  (fn _ => [ (simp_tac (esimps [uca_ext.eq_norm, uc_pext_alt]) 1),
    (simp_tac (esimps [Union_subset, uc_prod_def, uc_swap_ea]) 1) ]) ;

(* following two ought to be true! *)
val _ = qed_goal "ang_ch_Union" Dch.thy 
  "ang_ch (Union Css) = ang_ch (ang_ch ` Css)"
  (fn _ => [ (rtac ext 1),
    (simp_tac (esimps [ang_ch_def, uca_ext.eq_norm, UN_im_uc_of]) 1) ]) ;

val _ = qed_goal "dem_ch_Union" Dch.thy 
  "dem_ch (Union Css) = dem_ch (dem_ch ` Css)"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_dem]) 1) ]) ;

val _ = qed_goal "seq_dem_chL" Dch.thy
  "seq_ch (dem_ch Cs) B = dem_ch ((%C. seq_ch C B) ` Cs)"
  (fn _ => [ (rtac wp_ch_inj_ext 1), 
    (simp_tac (esimps [wp_ch_seq, wp_ch_dem]) 1) ]) ; 

val _ = qed_goal "seq_ang_chL" Dch.thy
  "seq_ch (ang_ch Cs) B = ang_ch ((%C. seq_ch C B) ` Cs)"
  (fn _ => [ (rtac wp_ch_inj_ext 1), 
    (simp_tac (esimps [wp_ch_seq, wp_ch_ang]) 1) ]) ; 

(* the above two results are also
  (ext B o pext (%C. C s)) Cs = pext (ext B o (%C. C s)) Cs,
  (ext B o extSet (%C. C s)) Cs = extSet (ext B o (%C. C s)) Cs,
  note the similar pattern of these two *) 
val _ = qed_goal "seq_dem_chL" Dch.thy
  "seq_ch (dem_ch Cs) B = dem_ch ((%C. seq_ch C B) ` Cs)"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [seq_ch_def, extU_alt, dem_ch_def, uca_ext.eq_norm]) 1),
    (simp_tac (esimps [mk_sap uc_P14eo, mk_sap uc_pextomap]) 1), 
    cong_tac 1, (rtac ext 1), 
    (simp_tac (esimps [seq_ch_def, extU_alt, uca_ext.eq_norm]) 1) ]) ;

val _ = qed_goal "seq_ang_chL" Dch.thy
  "seq_ch (ang_ch Cs) B = ang_ch ((%C. seq_ch C B) ` Cs)"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [seq_ch_def, extU_alt, ang_ch_def, uca_ext.eq_norm]) 1),
    (simp_tac (esimps [uc_EC, symmetric extSet_def, mk_sap MonadSet.E3']) 1),
    cong_tac 1, (rtac ext 1), Simp_tac 1 ]) ;

(* doubt whether the corresponding right side rules hold,
  difference in the order of demon and angel making choices *)

val _ = qed_goal "conjugate_conjugate" Dch.thy 
  "conjugate (conjugate A) = A" 
  (fn _ => [ (rtac ext 1), (simp_tac (esimps
      [conjugate_def, uca_ext.eq_norm, mk_ap swap_o_swap]) 1) ]) ;
    
val _ = qed_goalw "fis_conjugate" Dch.thy [fis_ch_alt, trm_ch_alt]
  "fis_ch (conjugate A) = trm_ch A"
  (fn _ => [ (simp_tac (esimps [wp_conjugate]) 1),
    (rtac ext 1), Simp_tac 1, cong_tac 1, (rtac ext 1), Simp_tac 1 ]) ;

val _ = qed_goalw "trm_conjugate" Dch.thy [fis_ch_alt, trm_ch_alt]
  "trm_ch (conjugate A) = fis_ch A"
  (fn _ => [ (simp_tac (esimps [wp_conjugate]) 1),
    (rtac ext 1), Simp_tac 1, cong_tac 1, (rtac ext 1), Simp_tac 1 ]) ;

val _ = qed_goalw "conjugate_swU" Dch.thy [swU_def] "conjugate B == swU o B"
  (fn _ => [ (rtac meta_ext 1), (simp_tac (esimps [conjugate_def]) 1) ]) ;

val _ = qed_goal "seq_conjugate" Dch.thy
  "seq_ch (conjugate B) (conjugate C) = conjugate (seq_ch B C)"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_seq, wp_conjugate, o_assoc, Not_o_Not]) 1) ]) ; 

(* or from swU being a monad morphism *)
val _ = qed_goalw "seq_conjugate" Dch.thy [conjugate_swU]
  "seq_ch (conjugate B) (conjugate C) = conjugate (seq_ch B C)"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [seq_ch_def, swU_mm]) 1) ]) ;

fun icon th = simplify (HOL_ss addsimps [conjugate_conjugate])
  (read_instantiate [("A", "conjugate ?A1")] th RS sym) ;

val _ = qed_goal "conjugate_ang_ch" Dch.thy 
  "conjugate (ang_ch As) = dem_ch (conjugate ` As)"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_dem, wp_ch_ang, wp_conjugate]) 1) ]) ;

val _ = qed_goal "conjugate_dem_ch" Dch.thy 
  "conjugate (dem_ch As) = ang_ch (conjugate ` As)"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_dem, wp_ch_ang, wp_conjugate]) 1) ]) ;

val _ = qed_goalw "wp_ch_precon" Dch.thy [precon_ch_def, wp_ch_def]
  "wp_ch (precon_ch P A) Q s = (P s & wp_ch A Q s)"
  (fn _ => [ (simp_tac (esimps [uca_ext.eq_norm]) 1) ]) ;

val _ = qed_goalw "wp_ch_guard" Dch.thy [guard_ch_def, wp_ch_def]
  "wp_ch (guard_ch P A) Q s = (P s --> wp_ch A Q s)"
  (fn _ => [ (auto_tac (cesimps [uca_ext.eq_norm])) ]) ;

val _ = qed_goal "conjugate_precon" Dch.thy
  "conjugate (precon_ch P A) = guard_ch P (conjugate A)"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_precon, wp_ch_guard, wp_conjugate]) 1) ]) ;

val _ = qed_goal "conjugate_guard" Dch.thy
  "conjugate (guard_ch P A) = precon_ch P (conjugate A)"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_precon, wp_ch_guard, wp_conjugate]) 1) ]) ;

val _ = qed_goal "precon_ch_trm" Dch.thy
  "precon_ch (trm_ch A) A = A"
  (fn _ => [ (rtac ext 1), 
    (clarsimp_tac (cesimps [precon_ch_def, trm_ch_def]) 1),
    (etac uca_ext.Rep_inverse' 1) ]) ;

val _ = qed_goal "guard_ch_fis" Dch.thy
  "guard_ch (fis_ch A) A = A"
  (fn _ => [ (rtac ext 1), 
    (clarsimp_tac (cesimps [guard_ch_def, fis_ch_def]) 1),
    (rtac uca_ext.Rep_inverse' 1), 
    (etac (Rep_is_uc RS empty_in_uc) 1) ]) ;

val _ = qed_goalw "prd_ch_by_conjugate" Dch.thy 
  [prd_ch_def, conjugate_def, uc_swap_def]
  "prd_ch s' A s = ({s'} : Rep_uca (conjugate A s))" 
  (fn _ => [ (simp_tac (esimps [uca_ext.eq_norm]) 1), 
    Safe_tac, (rtac uc_inI 1), Simp_tac 1,
    (datac bspec 1 1 THEN Fast_tac 1) ]) ;

val _ = bind_thm ("crd_ch_conjugate", 
  fold_rule [crd_ch_def] prd_ch_by_conjugate RS sym) ; 
val _ = bind_thm ("prd_ch_conjugate", icon crd_ch_conjugate) ;

val _ = qed_goal "prd_ch_alt" Dch.thy 
  "prd_ch s' A == Not o wp_ch A (%s. s ~= s')"
  (fn _ => [ (rtac meta_ext 1), 
    (simp_tac (esimps [prd_ch_def, wp_ch_def]) 1), Safe_tac, 
    (REPEAT (datac bspec 1 1 THEN Fast_tac 1)) ]) ;

val _ = qed_goal "crd_ch_alt" Dch.thy 
  "crd_ch s' A == wp_ch A (%s. s = s')"
  (fn _ => [ (rtac meta_ext 1), 
    (simp_tac (esimps [crd_ch_def, wp_ch_def]) 1), Safe_tac, 
    (etac rev_bexI 1), (datac uc_of.I 1 2), Auto_tac ]) ;

val _ = qed_goal "pod_ch_alt" Dch.thy 
  "pod_ch u M == Not o wp_ch M (%m. m ~: u)"
  (fn _ => [ (rtac meta_ext 1),
    (simp_tac (esimps [pod_ch_def, wp_ch_def, uc_swap_def]) 1), 
    Safe_tac, (ALLGOALS uc_tac) ]) ;

val _ = qed_goal "cod_ch_alt" Dch.thy 
  "cod_ch u M == wp_ch M (%m. m : u)"
  (fn _ => [ (rtac meta_ext 1),
    (simp_tac (esimps [cod_ch_def, wp_ch_def]) 1), Safe_tac, 
    Fast_tac 1, (datac uc_of.I 1 1), Full_simp_tac 1 ]) ;

val _ = qed_goalw "pod_ch_conjugate" Dch.thy 
  [pod_ch_alt, cod_ch_alt, wp_conjugate]
  "pod_ch u (conjugate A) = cod_ch u A"
  (fn _ => [ (rtac ext 1), Simp_tac 1, cong_tac 1, (rtac ext 1), Simp_tac 1 ]) ;
val _ = bind_thm ("cod_ch_conjugate", icon pod_ch_conjugate) ;

(* normal forms *)
val _ = qed_goal "dem_nf" Dch.thy
  "M = dem_ch (range (%u. guard_ch (pod_ch u M) \
    \ (ang_ch (range (%m'. precon_ch (%x. m' : u) (%m. unitU m'))))))"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_precon, wp_ch_guard, wp_ch_dem, wp_ch_ang,
        pod_ch_def, unitU_def]) 1), 
    (fold_goals_tac [Ball_def, Bex_def]),
    (simp_tac (esimps [uc_swap_ae]) 1),
    (clarsimp_tac (cesimps [wp_ch_def, uca_ext.eq_norm, Ex_uc_lem]) 1),
    (simp_tac (esimps [in_Collect]) 1) ]) ;

val _ = qed_goal "ang_nf" Dch.thy
  "M = ang_ch (range (%u. precon_ch (cod_ch u M) \
    \ (dem_ch (range (%m'. guard_ch (%x. m' : u) (%m. unitU m'))))))"
  (fn _ => [ (rtac wp_ch_inj 1), (REPEAT (rtac ext 1)),
    (simp_tac (esimps [wp_ch_precon, wp_ch_guard, wp_ch_dem, wp_ch_ang,
        cod_ch_def, unitU_def]) 1), 
    (simp_tac (esimps [wp_ch_def, uca_ext.eq_norm, Ex_uc_lem]) 1),
    (fold_goals_tac [Ball_def, Bex_def]),
    (simp_tac (esimps [in_Collect]) 1) ]) ;

(* to get the substitution as ('a => 'b uca) from a monotonic predicate
  transformer, see Chorus Angelorum, pg 9, last para *)

(* sub_of_pt in terms of KtoSS *)
val _ = qed_goalw "sub_fam" Dch.thy [sub_of_pt_def, KtoSS_alt]
  "sub_of_pt F s == uc_Abs (KtoSS (%f. F f s))" fn_at ;

val eval_of_fam_lem' = [eq_commute,
  read_instantiate [("c", "%f. ?F f ?s")] eval_of_fam_lem] MRS trans ;

val _ = qed_goal_spec_mp "sub_of_pt_lem" Dch.thy "S = sub_of_pt F --> \
    \ (ALL P. (P ---> Q) --> (F P ---> F Q)) = (F Q = wp_ch S Q)"
  (fn _ => [ (rtac impI 1), hyp_subst_tac 1, 
    (auto_tac (cesimps [expand_fun_eq, o_def, eval_of_fam_lem',
      wp_ch_evalU, sub_fam, C_evalU_def, uca_ext.eq_norm])) ]) ;

val _ = qed_goalw_spec_mp "sub_of_pt" Dch.thy [mono_pt_def]
  "S = sub_of_pt F --> mono_pt F = (F = wp_ch S)"
  (fn _ => [ (rtac impI 1), hyp_subst_tac 1, (stac expand_fun_eq 1),
    (auto_tac (cesimps [sub_of_pt_lem RS sym])) ]);

val _ = bind_thm ("wp_ch_sub", refl RS sub_of_pt RS iffD1 RS sym) ;

val _ = qed_goal "sub_of_wp" Dch.thy "sub_of_pt (wp_ch S) = S"
  (fn _ => [ (rtac wp_ch_inj 1), (rtac wp_ch_sub 1),
    (rewtac mono_pt_def), (strip_tac 1), (etac wp_ch_li_mono 1) ]) ;
Addsimps [sub_of_wp] ;

val _ = qed_goalw "dem_ch_glb" Dch.thy [ref_ch_def, liftimp]
  "(ALL C:Cs. ref_ch B C) = ref_ch B (dem_ch Cs)"
  (fn _ => [ (auto_tac (cesimps [wp_ch_dem])) ]) ; 

val _ = qed_goalw "ang_ch_lub" Dch.thy [ref_ch_def, liftimp]
  "(ALL C:Cs. ref_ch C B) = ref_ch (ang_ch Cs) B"
  (fn _ => [ (auto_tac (cesimps [wp_ch_ang])) ]) ; 

val _ = qed_goalw "strongest_guard_ch_lem" Dch.thy [guard_ch_def, fis_ch_def]
  "(guard_ch g A s = A s) = (fis_ch A s --> g s)"
  (fn _ => [ (simp_tac (esimps [uca_ext.inverse_norm,
    uca_ext.norm_Rep RS uc_is_UNIV]) 1) ]) ;
  
val _ = qed_goalw "strongest_guard_ch" Dch.thy [liftimp]
  "(guard_ch g A = A) = (fis_ch A ---> g)"
  (fn _ => [ (simp_tac (esimps [strongest_guard_ch_lem RS sym]) 1),
    Safe_tac, (rtac ext 2), Auto_tac ]) ;
    
val _ = qed_goalw "strongest_precon_ch_lem" Dch.thy [precon_ch_def, trm_ch_def]
  "(precon_ch g A s = A s) = (trm_ch A s --> g s)"
  (fn _ => [ (simp_tac (esimps [uca_ext.inverse_norm]) 1) ]) ;
    
val _ = qed_goalw "strongest_precon_ch" Dch.thy [liftimp]
  "(precon_ch g A = A) = (trm_ch A ---> g)"
  (fn _ => [ (simp_tac (esimps [strongest_precon_ch_lem RS sym]) 1),
    Safe_tac, (rtac ext 2), Auto_tac ]) ;
    


