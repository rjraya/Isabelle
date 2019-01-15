
structure Dtcv = struct val thy = theory "Dtcv" end ;
val _ = use_legacy_bindings Dtcv.thy ;

val defs_tcv = [prdf_tc_def, assignvs_tc_def, revert_tc_def] @ defs_tcm ;

val _ = qed_goalw "ass_wp_tc" Dtcv.thy 
  [assignv_tc_def, assigne_tc_def, wp_tc_def]
  "wp_tc (assigne_tc x E) Q st = Q (st (x := E st))" fn_at ;

AddSEs [wp_imp_trm_tc'] ;

val _ = qed_goalw_spec_mp "frame_tc_chst" Dtcv.thy [chst_def, frame_tc_def]
  "frame_tc C f --> C s = Term S --> s' : S --> (s, s') : chst f" fn_at ;

val _ = qed_goalw_spec_mp "frame_tc_indep" Dtcv.thy [indep_def]
  "frame_tc C F --> indep F Q --> C s = Term S --> s' : S --> Q s' = Q s"
  (fn _ => [ (Clarify_tac 1), (datac frame_tc_chst 2 1), Force_tac 1 ]) ;

(* Steve Dunne. A Theory of Generalised Substitutions.  ZB 2002, LNCS 2272 
  pg 282, GS3 *)

val _ = qed_goal_spec_mp "GS3" Dtcv.thy 
  "frame_tc S F --> indep F Q --> \
    \ wp_tc S Q s = (trm_tc S s & (fis_tc S s --> Q s))"
  (fn _ => [ Safe_tac, 
    (rtac (fis_or_wp_tc RS disjE) 2), atac 3, contr_tac 2,
    (ALLGOALS (clarsimp_tac (ces [nonemptyE],
      esimps [wp_tc_def, fis_tc_def]))),
    (case_tac "S s" 2), (force_tac (cesimps [trm_tc_def]) 2),
    (rtac exI 2), Safe_tac, atac 3,
    (ALLGOALS (datac frame_tc_indep 3)), Auto_tac ]) ;

(* pg 285, Prop'n 3 *)
val _ = qed_goal_spec_mp "prop3" Dtcv.thy 
  "frame_tc S F --> indep F R --> \
    \ wp_tc S (Q V R) = (wp_tc S Q V (trm_tc S && R))"
  (fn _ => [ (safe_tac (cis [ext] addSss esimps [wp_tc_def, trm_tc_def])),
    Force_tac 2, (datac frame_tc_indep 3 1), Force_tac 1,
    (case_tac "S x" 1), (contr_tac 1),
    (rtac exI 1), Safe_tac, atac 2,
    (datac frame_tc_indep 3 1), Auto_tac ]) ;

val _ = qed_goalw "prdf_tc_imp_fis" Dtcv.thy [liftimp, prdf_tc_def] 
  "prdf_tc vars s' S ---> fis_tc S"
  (fn _ => [ Auto_tac, (rtac (fis_or_wp_tc RS disjE) 1), Auto_tac ]) ;

val _ = qed_goalw "trm_or_prdf_tc" Dtcv.thy 
  [prdf_tc_def, wp_tc_def, mk_eq trm_alt, o_def] 
  "trm_tc S s | prdf_tc vars s' S s" fn_at ;

(* do we want this? - just consider ACNF_tc as though frame is all vars 
val _ = qed_goal "ACNFf_tc" Dtcv.thy 
  "(revert_tc (- vars) A) = (precon_tc (trm_tc A) \
    \ (at_tc (%s'. guard_tc (prdf_tc vars s' A) (assignvs_tc vars s'))))"
  (fn _ => [ rtac ext 1, (case_tac "A x" 1),
    (ALLGOALS (asm_simp_tac (esimps 
      [revert_tc_def, precon_tc_def, trm_tc_def, at_tc_def]))),
    (safe_tac (claset () addSss (esimps (choice_tc_def'' :: defs_tcv)
      addsplits [split_if_asm]))),
    (etac swap 2), (etac notE 2), 
    (etac rev_image_eqI 2), (rtac ext 2), 
    (force_tac (cesimps [setvars_def]) 2), 
    ]) ; *)

