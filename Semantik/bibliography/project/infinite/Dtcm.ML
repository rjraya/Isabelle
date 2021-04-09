
structure Dtcm = struct val thy = theory "Dtcm" end ;
val _ = use_legacy_bindings Dtcm.thy ;

val defs_tcm' = [ Let_def, trm_tc_def, wp_tc_def, fis_tc_def,
  concert_tc_def, pcomp_tc_def, pcomprs_tc_def, 
  at_tc_def, precon_tc_def, guard_tc_def, abort_tc_def, magic_tc_def] ; 

val defs_tcm = prd_tc_def :: defs_tcm' ;

val cs_tcm = cesimps defs_tcm ;

fun ft_tcm _ = [REPEAT (resolve_tac [set_ext, ext, impI] 1), auto_tac cs_tcm] ;

val ref_tc_def' = rewrite_rule [liftimp] ref_tc_def ;
val choice_tc_def' = rewrite_rule [pext_tc_def, o_def] choice_tc_def ;
val pcomp_tc_def' = rewrite_rule [pcomprs_tc_def] pcomp_tc_def ;
val choice_tc_def'' = rewrite_rule [prodtc_def] choice_tc_def' ;
val lub_pt_def' = rewrite_rule [Qcs_def] lub_pt_def ;

val _ = qed_goalw "ref_tc_refl" Dtcm.thy [ref_tc_def'] "ref_tc A A" fn_at ;
AddIffs [ref_tc_refl] ;

(* alternative characterisation of total correctness refinement *)
val _ = qed_goalw "ref_tc_alt" Dtcm.thy 
  [ref_tc_def, wp_tc_def, meta_eq_def, liftimp]
  "ref_tc A B == ALL s SA. A s = Term SA --> \
    \ (EX SB. SB <= SA & B s = Term SB)" 
  (fn _ => [ Safe_tac, (etac allE2 2), mp_tac 2, Clarify_tac 2,
    (rtac exI 2), (rtac conjI 2), atac 3, Fast_tac 2,
    (eres_inst_tac [("x", "%x. x : SA")] allE 1), Auto_tac ]) ;

(* link total correctness refinement here to abstract commands *)
val _ = qed_goalw "ref_tc_swap" Dtcm.thy [totcref_alt, ref_tc_alt]
  "totcref A B = ref_tc (swap_tc o A) (swap_tc o B)" 
  (fn _ => [ (simp_tac (esimps [swap_tc_def]) 1), Auto_tac,
    (etac allE 1), Auto_tac, 
    (res_inst_tac [("A", "A s")] oset_cases 1),
    (res_inst_tac [("A", "B s")] oset_cases 1), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "ref_tc_antisym" Dtcm.thy [ref_tc_alt]
  "ref_tc A B --> ref_tc B A --> A = B" 
  (fn _ => [Safe_tac, rtac ext 1, 
    (case_tac "A x" 1), (ALLGOALS (case_tac "B x")), 
    (REPEAT_SOME (etac allE2)), REPEAT_FIRST mp_tac, Auto_tac ]) ;

val _ = qed_goal_spec_mp "wp_tc_inj" Dtcm.thy 
  "wp_tc A = wp_tc B --> A = B" 
  (fn _ => [ (rtac impI 1), (rtac ref_tc_antisym 1),
    (rewtac ref_tc_def), Auto_tac ]) ;

val _ = qed_goalw "totceqv_alt_tcm" Dtcm.thy [totceqv_def, meta_eq_def]
  "totceqv A B == swap_tc o B = swap_tc o A"
  (fn _ => [ (auto_tac (cis [ref_tc_antisym], esimps [ref_tc_swap])) ]) ;

val _ = qed_goalw_spec_mp "Qcs_mono" Dtcm.thy [Qcs_def]
  "(Q ---> R) --> Qcs R <= Qcs Q" fn_at ;

val _ = qed_goalw_spec_mp "lub_pt_mono" Dtcm.thy [lub_pt_def]
  "(ALL T:Ts. (EX U:Us. T ----> U)) --> (Q ---> R) --> \
    \ (lub_pt Ts Q ---> lub_pt Us R)"
  (fn _ => [ Safe_tac, (dtac Qcs_mono 1), 
    (clarsimp_tac (cesimps [lub_pt_def]) 1), 
    (datac subsetD 1 1), (datac bspec 1 1), Fast_tac 1 ]) ;

val lub_pt_mono' = rotate_prems ~1
  (ObjectLogic.rulify_no_asm (simplify (esimps []) lub_pt_mono)) ; 

val _ = qed_goalw_spec_mp "ref_tc_TermD" Dtcm.thy [ref_tc_def', wp_tc_def]
  "ref_tc A B --> A z = Term SA --> (EX SB. SB<=SA & B z = Term SB)" 
  (fn _ => [ Safe_tac, (etac allE2 1), (etac impE 1), 
    (rtac exI 1), (rtac conjI 1), 
    (rtac (Collect_mem_eq RS equalityD2) 1), atac 1,
    Full_simp_tac 1 ]) ;

val _ = qed_goalw_spec_mp "ref_tc_NonTermD" Dtcm.thy [ref_tc_def', wp_tc_def]
  "ref_tc A B --> B z = NonTerm --> A z = NonTerm"
  (fn _ => [ (case_tac "A z" 1), ALLGOALS Force_tac ]) ;

val _ = qed_goalw_spec_mp "wp_tc_mono_cond" Dtcm.thy [wp_tc_def, liftimp]
  "(P ---> Q) --> (wp_tc A P ---> wp_tc A Q)" (fn _ => [Force_tac 1]) ;
val wp_tc_mono_cond' = rewrite_rule [liftimp] wp_tc_mono_cond ;
    
val _ = qed_goalw "wp_imp_trm_tc" Dtcm.thy [liftimp, trm_tc_def, wp_tc_def] 
  "wp_tc S Q ---> trm_tc S" fn_at ;

val wp_imp_trm_tc' = ObjectLogic.rulify (rewrite_rule [liftimp] wp_imp_trm_tc);

val _ = qed_goalw_spec_mp "choice_tc_NT" Dtcm.thy [choice_tc_def'']
  "A : As --> A s = NonTerm --> choice_tc As s = NonTerm"
  (fn _ => [ Safe_tac, (Simp_tac 1),
    (rtac image_eqI 1), atac 2, (asm_simp_tac (esimps [Let_def]) 1) ]) ;
AddSEs [insertI1 RS choice_tc_NT] ;

val _ = qed_goal "choice_tc_single" Dtcm.thy "choice_tc {C} = C"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [choice_tc_def', Let_def, P2]) 1) ]) ; 
Addsimps [choice_tc_single] ;

val _ = qed_goal "wp_abort_tc" Dtcm.thy "wp_tc abort_tc P s = False" ft_tcm ;
val _ = qed_goal "wp_magic_tc" Dtcm.thy "wp_tc magic_tc P s = True" ft_tcm ;
Addsimps [wp_abort_tc, wp_magic_tc] ;

val _ = qed_goal "abort_tc" Dtcm.thy "abort_tc = swap_tc o abort"
  (fn _ => [ (rtac ext 1),
    (simp_tac (esimps [abort_tc_def, abort_def, swap_tc_def]) 1) ]) ;

val _ = qed_goal "magic_tc" Dtcm.thy "magic_tc = swap_tc o magic"
  (fn _ => [ (rtac ext 1), (force_tac (cesimps 
      [magic_tc_def, magic_def, swap_tc_def]) 1) ]) ;

val _ = qed_goal "abort_alt" Dtcm.thy "abort_tc = precon_tc (%s. False) unit_tc"
  (fn _ => [ (rtac ext 1),
    (simp_tac (esimps [abort_tc_def, precon_tc_def]) 1) ]) ;

val _ = qed_goal "magic_alt" Dtcm.thy "magic_tc = guard_tc (%s. False) C"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [magic_tc_def, guard_tc_def]) 1) ]) ;

val _ = qed_goal "guard_tc" Dtcm.thy 
  "guard_tc P (swap_tc o C) = swap_tc o guard P C"
  (fn _ => [ (rtac ext 1), 
    (auto_tac (cesimps [guard_def, guard_tc_def, swap_tc_def])) ]) ;

val _ = qed_goal "guard_wp_tc" Dtcm.thy 
  "wp_tc (guard_tc P C) Q s = (P s --> wp_tc C Q s)"
  (fn _ => [ (simp_tac (esimps defs_tcm) 1) ]) ;
    
val _ = qed_goal "precon_tc" Dtcm.thy 
  "precon_tc P (swap_tc o C) = swap_tc o precon P C"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [precon_def, precon_tc_def, swap_tc_def]) 1) ]) ;

val _ = qed_goal "precon_wp_tc" Dtcm.thy 
  "wp_tc (precon_tc P C) Q = (P && wp_tc C Q)"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps defs_tcm) 1) ]) ;

val _ = bind_thm ("precon_wp_tc'", 
  rewrite_rule [liftand] (precon_wp_tc RS fun_cong)) ;

val _ = qed_goal "trm_tc" Dtcm.thy "trm_tc (swap_tc o C) = trmm C"
  (fn _ => [ (rtac ext 1), 
    (auto_tac (cesimps [trmm_def, trm_tc_def, swap_tc_def])) ]) ;

val _ = qed_goal "wp_tc" Dtcm.thy "wp_tc (swap_tc o C) = wpm C"
  (fn _ => [ (REPEAT (rtac ext 1)), 
    (simp_tac (esimps [wpm_def, wp_tc_def, trm_tc RS sym, trm_tc_def]) 1),
    Safe_tac, (case_tac "swap_tc (C xa)" 3),
    (rtac exI 4), rtac conjI 4, atac 5,
    (full_simp_tac (esimps [wlpm_def, swap_tc_def] addsplits [split_if_asm]) 4),
    (full_simp_tac (esimps [wlpm_def, swap_tc_def] addsplits [split_if_asm]) 1),
    (TRYALL Force_tac) ]) ;

val _ = qed_goal "seq_wp_tc" Dtcm.thy 
  "wp_tc (seq_tc A B) Q = wp_tc A (wp_tc B Q)"
  (fn _ => [ ioiotac, (simp_tac (esimps [wp_tc, seq_tc, seq_wp]) 1) ]) ;

(* seq_wp_tc gives seq_tc_assoc easily *)
val seq_assoc' = prove_goal Dtcm.thy 
  "seq_tc A (seq_tc B C) = seq_tc (seq_tc A B) C"
  (fn _ => [ (rtac ref_tc_antisym 1), 
    (auto_tac (cesimps [ref_tc_def, seq_wp_tc])) ]) ;

val _ = qed_goal "Xpre_tc" Dtcm.thy 
  "seq_tc (precon_tc P A) B = precon_tc P (seq_tc A B)" 
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [seq_tc_def', precon_tc_def]) 1)]);
  
val _ = qed_goal "Xguard_tc" Dtcm.thy 
  "seq_tc (guard_tc P A) B = guard_tc P (seq_tc A B)" 
  (fn _ => [ (rtac ext 1), (force_tac (cesimps 
        [seq_tc_def', guard_tc_def, prodtc_def]) 1)]);

val _ = qed_goal "choice_tc" Dtcm.thy 
  "choice_tc (comp swap_tc ` C) = swap_tc o choice C"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [choice_def, choice_tc_def, pext_tc_def]) 1),
    (stac (Union_image_eq RS sym) 1),
    (rtac trans 1), (rtac (mk_ap pext_swap') 2), 
    (Conv.CONV_TAC (SOME o eta_conversion : conv)),
    (cong_tac 1), (force_tac (cesimps [Let_def, image_def]) 1) ]) ;

val _ = qed_goal "choice_wp_tc" Dtcm.thy 
  "wp_tc (choice_tc Cs) Q state = (ALL C:Cs. wp_tc C Q state)"
  (fn _ => [ iocs2tac, 
    (simp_tac (esimps [wp_tc, choice_tc, choice_wp]) 1),
    (simp_tac (esimps [symmetric tcoiorw]) 1) ]) ;

val _ = qed_goalw "ref_tc_alt2" Dtcm.thy 
  [meta_eq_def, ref_tc_def, liftimp, wp_tc_def] "ref_tc A B == \
    \ ALL s. (EX SA SB. SB <= SA & A s = Term SA & B s = Term SB) | \
    \ A s = NonTerm"
  (fn _ => [ Safe_tac, (case_tac "A s" 1), contr_tac 1,
    (REPEAT_FIRST (eresolve_tac [allE, impE])), Safe_tac,
    (datac (sym RS trans) 1 4), Fast_tac 4, Force_tac 3,
    (REPEAT_FIRST (ares_tac [exI, conjI])), Asm_simp_tac 2,
    (rtac (Collect_mem_eq RS sym) 2), Fast_tac 1 ]) ;

val _ = qed_goalw "bot_abort_tc" Dtcm.thy [ref_tc_alt, abort_tc_def]
  "ref_tc abort_tc C" fn_at ;

val _ = qed_goalw "top_magic_tc" Dtcm.thy [ref_tc_alt, magic_tc_def]
  "ref_tc C magic_tc" (fn _ => [ Safe_tac, (case_tac "C s" 1), Auto_tac ]) ;

val _ = qed_goalw "choice_glb_tc" Dtcm.thy 
  [ref_tc_def, liftimp, mk_eq choice_wp_tc]
  "ref_tc A (choice_tc Cs) = (ALL C:Cs. ref_tc A C)" fn_at ;

val _ = bind_thm ("choice_ref_tc",
  ref_tc_refl RS (choice_glb_tc RS iffD1) RS bspec) ;

val _ = qed_goal "choice_empty_tc" Dtcm.thy "choice_tc {} = magic_tc"
  (fn _ => [ (rtac ref_tc_antisym 1), 
    (auto_tac (cesimps [top_magic_tc, choice_glb_tc])) ]) ;

val _ = qed_goal "choice_abort_tc" Dtcm.thy 
  "choice_tc (insert abort_tc S) = abort_tc" 
  (fn _ => [ (rtac ref_tc_antisym 1),
    (auto_tac (cesimps [ref_tc_def', choice_wp_tc])) ]) ;

val _ = qed_goal "choice_magic_tc" Dtcm.thy 
  "choice_tc (insert magic_tc S) = choice_tc S" 
  (fn _ => [ (rtac ref_tc_antisym 1),
    (auto_tac (cesimps [ref_tc_def', choice_wp_tc])) ]) ;

(* proofs of seq_choice_tcL and seq_choice_tcR from corresponding
  results for general correctness, shorter proofs below  
val _ = qed_goal "seq_choice_tcL" Dtcm.thy 
  "seq_tc (choice_tc Cs) B = choice_tc ((%C. seq_tc C B) ` Cs)"
  (fn _ => [ iocs2tac, 
    (simp_tac (esimps [seq_tc, choice_tc, seq_choiceL]) 1),
    (simp_tac (esimps [choice_tc RS sym]) 1), cong_tac 1, 
    Safe_tac, (REPEAT_FIRST (ares_tac [refl, image_eqI])),
    (auto_tac (cesimps [symmetric tcoiorw])) ]) ;

val _ = qed_goal_spec_mp "seq_choice_tcR" Dtcm.thy 
  "cs ~= {} --> seq_tc A (choice_tc cs) = choice_tc (seq_tc A ` cs)"
  (fn _ => [ (rtac impI 1), iocs2tac, 
    (asm_simp_tac (esimps [seq_tc, choice_tc]) 1),
    (stac seq_choiceR 1), Force_tac 1,
    (simp_tac (esimps [choice_tc RS sym]) 1), 
    (Conv.CONV_TAC (SOME o eta_conversion : conv)), cong_tac 1,
    (ALLGOALS (etac thin_rl)), Safe_tac,
    (REPEAT_FIRST (ares_tac [refl, image_eqI])),
    (auto_tac (cesimps [seq_tc RS sym, symmetric tcoiorw])),
    (auto_tac (cesimps [o_def])) ]) ;
*)

val _ = qed_goal "seq_choice_tcL" Dtcm.thy 
  "seq_tc (choice_tc Cs) B = choice_tc ((%C. seq_tc C B) ` Cs)"
  (fn _ => [ (rtac wp_tc_inj 1), (REPEAT (rtac ext 1)),
    (clarsimp_tac (cesimps [seq_wp_tc, choice_wp_tc]) 1) ]) ;
    
val _ = qed_goal_spec_mp "seq_choice_tcR" Dtcm.thy 
  "cs ~= {} --> seq_tc A (choice_tc cs) = choice_tc (seq_tc A ` cs)"
  (fn _ => [ (rtac impI 1), (rtac wp_tc_inj 1), (REPEAT (rtac ext 1)),
    (clarsimp_tac (cesimps [seq_wp_tc, choice_wp_tc]) 1),
    (safe_tac (claset () addSss esimps [wp_tc_def])),
    (case_tac "A xa" 2), Force_tac 2, 
    (force_tac (cesimps [choice_wp_tc]) 2),
    (datac subsetD 1 1), (clarsimp_tac (cesimps [choice_wp_tc]) 1),
    (clarsimp_tac (cesimps [wp_tc_def]) 1) ]) ;

val _ = qed_goal "fis_tc" Dtcm.thy "fis_tc (swap_tc o C) = fis C"
  (fn _ => [ (rtac ext 1), 
    (auto_tac (cesimps [fis_def, fis_tc_def, swap_tc_def])),
    (case_tac "xa" 1), Auto_tac]) ;

val _ = qed_goal "concert_tc" Dtcm.thy 
  "concert_tc A B = swap_tc o (conc (swap_gc o A) (swap_gc o B))"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [concert_tc_def, conc_def, concrs_def, swap_tc_def]) 1),
    (case_tac "A x" 1), (ALLGOALS (case_tac "B x")), Auto_tac ]) ;

(** section 5 **)

val _ = qed_goal "trm_alt" Dtcm.thy "trm_tc C = (wp_tc C (%s. True))"
  (fn _ => [ (rtac ext 1), (case_tac "C x" 1),
    (ALLGOALS (asm_simp_tac (esimps [trm_tc_def, wp_tc_def]))) ]) ;

val _ = qed_goal "fis_alt" Dtcm.thy "fis_tc C = Not o (wp_tc C (%s. False))"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [fis_tc_def, wp_tc_def]) 1) ]) ;

val _ = qed_goal "fis_or_wp_tc" Dtcm.thy "fis_tc S s | wp_tc S Q s" ft_tcm ;
val _ = qed_goal "pc_trm_tc" Dtcm.thy "precon_tc (trm_tc A) A = A" ft_tcm ;
val _ = qed_goal "fis_guard_tc" Dtcm.thy "guard_tc (fis_tc A) A = A" ft_tcm ;

val _ = qed_goal_spec_mp "strongest_pc" Dtcm.thy 
  "(precon_tc pc A = A) = (trm_tc A ---> pc)" 
  (fn _ => [ (auto_tac (cis [ext], esimps 
      [fun_cong_all, precon_tc_def, trm_tc_def] addsplits [split_if_asm])),
    (TRYALL Force_tac) ]) ;

val _ = qed_goal_spec_mp "strongest_guard" Dtcm.thy 
  "(guard_tc g A = A) = (fis_tc A ---> g)" 
  (fn _ => [ (auto_tac (cis [ext], esimps 
      [fun_cong_all, guard_tc_def, fis_tc_def] addsplits [split_if_asm])),
    (TRYALL Force_tac) ]) ;

val _ = qed_goal "trm_guard_tc" Dtcm.thy 
  "trm_tc (guard_tc P C) s = (P s --> trm_tc C s)"
  (fn _ => [ (simp_tac (esimps [trm_alt, guard_wp_tc]) 1) ]) ;

val _ = qed_goal "trm_precon_tc" Dtcm.thy 
  "trm_tc (precon_tc P C) = (P && trm_tc C)" 
  (fn _ => [ (simp_tac (esimps [trm_alt, precon_wp_tc]) 1) ]) ;

val _ = qed_goal "trm_choice_tc" Dtcm.thy 
  "trm_tc (choice_tc Cs) s = (ALL C:Cs. trm_tc C s)" 
  (fn _ => [ (simp_tac (esimps [trm_alt, choice_wp_tc]) 1) ]) ;

(** section 7 - refinement, monotonocity **)
val _ = qed_goalw_spec_mp "precon_tc_ref_mono" Dtcm.thy [ref_tc_def]
  "(P--->Q) --> ref_tc A B --> ref_tc (precon_tc P A) (precon_tc Q B)" ft_tcm ;
val _ = qed_goalw_spec_mp "guard_tc_ref_mono" Dtcm.thy [ref_tc_def]
  "(Q ---> P) --> ref_tc A B --> ref_tc (guard_tc P A) (guard_tc Q B)" ft_tcm ;

val _ = qed_goalw_spec_mp "seq_tc_ref_mono" Dtcm.thy [ref_tc_def]
  "ref_tc A1 B1 --> ref_tc A2 B2 --> ref_tc (seq_tc A1 A2) (seq_tc B1 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [seq_wp_tc]) 1),
    (etac allE2 1 THEN mp_tac 1), 
    (etac allE 1), (dtac wp_tc_mono_cond' 1), Fast_tac 1 ]) ;

val _ = qed_goalw_spec_mp "conc_tc_not_ref_mono" Dtcm.thy [ref_tc_def']
  "A2 = magic_tc --> B2 = magic_tc --> A1 = abort_tc --> B1 = unit_tc --> \
    \ ~ (ref_tc A1 B1 --> ref_tc A2 B2 --> \
      \ ref_tc (concert_tc A1 A2) (concert_tc B1 B2))"
  (fn _ => [ (auto_tac (cesimps defs_tcm)) ]) ;

val _ = qed_goalw_spec_mp "choice_tc_ref_mono" Dtcm.thy [ref_tc_def]
  "(ALL s:S. ref_tc (f s) (g s)) --> \
    \ ref_tc (choice_tc (f ` S)) (choice_tc (g ` S))"
  (fn _ => [ (force_tac (cesimps [choice_wp_tc]) 1) ]) ;

(* generalised conjunctivity, only for non-empty conjunctions, 
  Dunne, pg 282, GS2 *)
val _ = qed_goalw_spec_mp "wp_tc_gen_conj'" Dtcm.thy [wp_tc_def, conj_pt_def]
  "Q : Qs --> conj_pt (wp_tc C) Qs s"
  (fn _ => [Safe_tac, (datac rev_bspec 1 2), Safe_tac, 
    (safe_tac (cis [exI])), (TRYALL atac), (datac bspec 1 2), Auto_tac ]) ; 

val _ = bind_thm ("wp_tc_gen_conj",
  rewrite_rule [conj_pt_def] wp_tc_gen_conj') ;

val _ = qed_goalw "pcomprs_tc2" Dtcm.thy [pcomprs_tc_def, pcomprs_def]
  "pcomprs_tc {swap_tc A, swap_tc B} = swap_tc (pcomprs A B)"
  (fn _ => [ (simp_tac (esimps [swap_tc_def]) 1), Auto_tac ]);

val _ = qed_goal "pcomp_tc2" Dtcm.thy 
  "pcomp_tc {swap_tc o A, swap_tc o B} = swap_tc o pcomp A B"
  (fn _ => [ (rtac ext 1),
    (simp_tac (esimps [pcomp_def, pcomp_tc_def]) 1), (rtac pcomprs_tc2 1) ]) ;

(* alternative proof below *)
val _ = qed_goal "pcomp_choice_tc" Dtcm.thy 
  "pcomp_tc {B, choice_tc (insert A As)} = \
    \ choice_tc ((%a. pcomp_tc {B, a}) ` insert A As)"
  (fn _ => [ iocs2tac,
    (simp_tac (HOL_ss addsimps [image_insert RS sym, image_empty,
      pcomp_tc2, choice_tc]) 1),
    (simp_tac (esimps [pcomp_choice, pcomp_tc2, choice_tc RS sym,
      symmetric tcoiorw, image_compose RS sym]) 1),
    cong_tac 1, (rtac ext 1), (simp_tac (esimps [symmetric tcoiorw]) 1) ]) ;

(*
val _ = qed_goalw_spec_mp "wp_tc_gen_conj" Dtcm.thy [wp_tc_def]
  "Q : Qs --> wp_tc C (%s. ALL Q : Qs. Q s) s = (ALL Q : Qs. wp_tc C Q s)" 
  (fn _ => [Safe_tac, (datac rev_bspec 1 2), Safe_tac, 
    (safe_tac (cis [exI])), (TRYALL atac), (datac bspec 1 2), Auto_tac ]) ; 
*)

val cslem = prove_goalw Dtcm.thy [meta_eq_def]
  "Q == (%s. ALL Q': (% x y. y ~= x) ` (- (Collect Q)). Q' s)" ft_tcm ;

val wplem = simplify init_ss (prd_tc_def RS def_imp_eq RS fun_cong RS 
  read_instantiate [("f", "Not")] arg_cong) RS sym ;

val _ = qed_goal_spec_mp "wp_prd_tc'" Dtcm.thy 
  "Q ~= (%s. True) --> wp_tc A Q s = (ALL Q':- Collect Q. ~ prd_tc Q' A s)"
  (fn _ => [ (rtac impI 1),
    let open Conv in (CONV_GOAL_TAC (CONCL_CONV
      (BUSTOP_CONV (NTH_CONV [1] (EQ_CONV (true, true) cslem)))) 1) end,
    (etac swap 1), (rtac ext 1), (etac swap 1), 
    (rtac trans 1), (rtac wp_tc_gen_conj 1), Force_tac 1,
    (simp_tac (esimps [wplem]) 1) ]) ; 
  
val _ = qed_goalw "Q_conj" Dtcm.thy [Qcs_def]
  "Q x = (ALL Q': Qcs Q. Q' x)" fn_at ;

val _ = bind_thm ("QcsD", rotate_prems 1 (Q_conj RS iffD1 RS bspec)) ;

val _ = qed_goalw_spec_mp "lub_pt_ub" Dtcm.thy 
  [mono_pt_def, liftimp, lub_pt_def, Qcs_def]
  "mono_pt T --> T : Ts --> (T Q ---> lub_pt Ts Q)"
  (fn _ => [ Clarsimp_tac 1, (datac bspec 1 1),
    (rtac (notI RS notnotD) 1), (etac allE2 1), (etac impE 1), 
    (etac allE 2), mp_tac 2, contr_tac 2, Fast_tac 1 ]) ;

val _ = qed_goalw_spec_mp "mono_pt_conj" Dtcm.thy [conj_pt_def, mono_pt_def]
  "(ALL Qs s. conj_pt T Qs s) --> mono_pt T"
  (fn _ => [ (Auto_tac), (eres_inst_tac [("xa", "{Q,R}")] allE2 1),
    Auto_tac, (etac notE 1), (chop_tac 1 (etac rev_iffD1 1)),
    cong_tac 1, rtac ext 1, Auto_tac ]) ;

val _ = qed_goalw_spec_mp "lub_pt_lub" Dtcm.thy [lub_pt_def] 
  "(ALL Qs. conj_pt T Qs s) --> \
    \ (ALL U:Us. ALL Q. U Q s --> T Q s) --> (ALL Q. lub_pt Us Q s --> T Q s)" 
  (fn _ => [ Safe_tac, (eres_inst_tac [("x", "Qcs Q")] allE 1),
    (full_simp_tac (esimps [conj_pt_def, Q_conj RS sym]) 1),
    (* (clarsimp_tac (cesimps [conj_pt_def, Q_conj RS sym]) 1)
      does something really weird *)
    Fast_tac 1 ]) ;

val _ = qed_goalw "lub_pt_is_conj" Dtcm.thy [lub_pt_def, conj_pt_def, Qcs_def] 
  "conj_pt (lub_pt Ts) Qs s" fn_at ;

val _ = qed_goal "pclem0" Dtcm.thy 
  "(S<={st. st ~= s'}) = (s' ~: S)" fn_at ;

val _ = qed_goal "pclem1" Dtcm.thy 
  "(ALL S. f S --> Y ~= S) = (~ f Y)" fn_at ;

val _ = qed_goal "pclem" Dtcm.thy 
  "(ALL S. S <= {st. st ~= s'} --> Y ~= S) = (s' : Y)" fn_at ;

Addsimps [pclem0, pclem] ;

val pc_css = (claset (), esimps
    [choice_tc_def'', guard_tc_def, Union_def, Let_def, 
      wp_tc_def, UN_subset_iff, sts_of_ocs.defs] addsplits [split_if_asm]) ;

val _ = qed_goalw "pc_aux_alt1" Dtcm.thy
  [pc_aux_def, at_tc_def, choice_tc_def'']
  "pc_aux Cs x = Term (Collect (%s. ALL C:Cs. prd_tc s C x))"
  (fn _ => [ (Simp_tac 1), Safe_tac,
    (clarsimp_tac pc_css 3), (rtac exI 3), rtac conjI 3, 
    (REPEAT_FIRST (match_tac [image_eqI, UNIV_I])), (rtac refl 4),
    (rtac singletonI 4), (auto_tac pc_css) ]) ;

val _ = qed_goal "pc_aux_alt2" Dtcm.thy 
  "pc_aux Cs s = Term (Inter (sts_of_ocs ((%C. C s) ` Cs)))"
  (fn _ => [ (simp_tac (esimps [pc_aux_alt1, prd_tc_def, wp_tc_def]) 1),
    (auto_tac pc_css), (dtac sym 2), (TRYALL Force_tac) ]) ;

val _ = qed_goal "pc_aux_wp" Dtcm.thy 
  "wp_tc (pc_aux Cs) = lub_pt (wp_tc ` Cs)"
  (fn _ => [ (REPEAT (rtac ext 1)),
    (simp_tac (esimps [lub_pt_def, Qcs_def, wp_tc_def, pc_aux_alt2]) 1),
    Safe_tac, (clarsimp_tac (cesimps [sts_of_ocs.defs]) 2),
    (rtac (notI RS notnotD) 2), (dtac bspec 2), Fast_tac 2,
    Clarify_tac 2, (dtac sym 2), Force_tac 2,
    (dtac subsetD 1), Full_simp_tac 2, Force_tac 1 ]) ;

(* Dunne, A Theory of Generalised Substitutions. ZB2002 s 6 
  prd, total correctness monad, no reference to frames *)

val _ = qed_goalw "prd_tc_alt" Dtcm.thy 
  [meta_eq_def, trm_tc_def, wp_tc_def, prd_tc_def, o_def]
  "prd_tc s' C s == trm_tc C s --> (EX S. C s = Term S & s' : S)" 
  (fn _ => [ (case_tac "C s" 1), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "prd_tc_alt'" Dtcm.thy [prd_tc_alt, trm_tc_def]
  "C s = Term S --> prd_tc s' C s = (s' : S)" fn_at ;

val _ = qed_goalw_spec_mp "trm_conj_pt" Dtcm.thy 
  [conj_pt_def, trm_tc_def, wp_tc_def]
  "trm_tc A s --> conj_pt (wp_tc A) Qs s"
  (fn _ => [ Safe_tac, (case_tac "A s" 2), Auto_tac ]) ;

val _ = qed_goalw "lub_tc" Dtcm.thy 
  [ref_tc_def, liftimp, mk_eq precon_wp_tc, mk_eq pc_aux_wp]
  "ref_tc (precon_tc (%s. EX C:Cs. trm_tc C s) (pc_aux Cs)) A = \
    \ (ALL C:Cs. ref_tc C A)"
  (fn _ => [ Safe_tac, (etac allE2 1), (etac mp 1), 
    (force_tac (ces [rev_bexI, QcsD], 
      esimps (subset_def :: lub_pt_def :: defs_tcm)) 1),

    (Clarsimp_tac 1), (etac (rotate_prems 2 lub_pt_lub) 1), 
    Fast_tac 2, Safe_tac, (rtac trm_conj_pt 1),
    (auto_tac (cesimps [trm_alt])) ]) ;

(*
val lttacs = [ (datac rev_bspec 1 1),
  (etac allE2 1), (etac impE 1), (rtac exI 1),
  (rtac conjI 1), atac 2, (rtac (Collect_mem_eq RS equalityD2) 1)] ;

val _ = qed_goalw "lub_tc" Dtcm.thy [ref_tc_def, liftimp, mk_eq precon_wp_tc]
  "ref_tc (precon_tc (%s. EX C:Cs. trm_tc C s) (pc_aux Cs)) A = \
    \ (ALL C:Cs. ref_tc C A)"
  (fn _ => [ Safe_tac, (etac allE2 1), (etac mp 1), 
    (clarsimp_tac (ces [rev_bexI], esimps (pc_aux_alt1 :: defs_tcm)) 1),
    Safe_tac, ((dtac subsetD THEN_ALL_NEW Fast_tac) 2),
    (etac rev_bexI 1), Force_tac 1,

    (clarsimp_tac (claset (), esimps (pc_aux_alt1 :: defs_tcm)
      addsplits [split_if_asm]) 1),
    (case_tac "C s" 1), (contr_tac 1), EVERY lttacs, 
    Safe_tac, (rtac exI 1), (rtac conjI 1), atac 2, 
    (rtac order_trans 1), atac 2, Safe_tac, EVERY lttacs, Auto_tac]) ;
*)

val lub_tc_single = simplify (esimps [pc_aux_def])
  (read_instantiate [("Cs", "{?C}")] lub_tc) ;
val _ = bind_thm ("ACNF_tc", 
  [ref_tc_refl] RL ([lub_tc_single] RL iffDs) MRS ref_tc_antisym) ;

val _ = qed_goalw_spec_mp "gs_of_pt" Dtcm.thy [gs_of_pt_def]
  "T = wp_tc C --> C = gs_of_pt T"
  (fn _ => [ Safe_tac, (rtac (ACNF_tc RS trans) 1),
    (simp_tac (esimps [trm_alt, prd_tc_def, o_def]) 1) ]) ;

(* if GS2 holds of a pt T then T is wp_tc (gs_of_pt T) *)
val _ = qed_goalw_spec_mp "pt_gc_gs" Dtcm.thy [gs_of_pt_def]
  "(ALL Q Qs s. Q : Qs --> conj_pt T Qs s) --> C = gs_of_pt T --> T = wp_tc C"
  (fn _ => [ Safe_tac, (REPEAT (rtac ext 1)),
    (simp_tac (esimps 
      [precon_wp_tc, guard_wp_tc, at_tc_def, choice_wp_tc, pc_aux_wp]) 1),
    (simp_tac (esimps [wp_tc_def]) 1),
    (case_tac "All x" 1), Asm_simp_tac 1, cong_tac 1,
    (rtac ext 1), Asm_simp_tac 1, Clarsimp_tac 1,
    (eres_inst_tac [("x", "insert (%s. True) (Qcs x)")] allE2 1),
    (etac impE 1), (force_tac (cesimps [Qcs_def]) 1),
    (eres_inst_tac [("x", "xa")] allE 1),
    (clarsimp_tac (cesimps [conj_pt_def, Qcs_def]) 1),
    (etac box_equals 1), (ALLGOALS cong_tac), (rtac ext 1), Auto_tac ]) ;

val _ = qed_goalw "pcomp_tc_alt" Dtcm.thy [meta_eq_def]
  "pcomp_tc Cs == precon_tc (%s. ALL C:Cs. trm_tc C s) (pc_aux Cs)"
  (fn _ => [ (rtac ext 1), 
    (clarsimp_tac (cesimps (pc_aux_alt1 :: defs_tcm)) 1), Safe_tac,
    Clarsimp_tac 2, (dres_inst_tac [("x", "S")] bspec 2), 
    (TRYALL (dtac sym THEN' Force_tac)) ]) ;

(*
val _ = qed_goal "pcomprs_NT" Dtcm.thy "pcomprs_tc S NonTerm = NonTerm"
  (fn _ => [ (case_tac "S" 1), Auto_tac ]) ;
Addsimps [pcomprs_NT] ;
*)

val _ = qed_goal "trm_pcomp_tc" Dtcm.thy 
  "trm_tc (pcomp_tc Cs) s = (ALL C:Cs. trm_tc C s)"
  (fn _ => [ (clarsimp_tac (cesimps [trm_tc_def, pcomp_tc_def']) 1),
    Safe_tac, (ALLGOALS (dtac sym THEN' Fast_tac)) ]) ;

val _ = qed_goalw "pcomp_wp_tc" Dtcm.thy [pcomp_tc_alt]
  "wp_tc (pcomp_tc Cs) Q s = ((ALL C:Cs. ?t C) & lub_pt ?z Q s)"
  (fn _ => [ (simp_tac (esimps 
      [precon_wp_tc, guard_wp_tc, at_tc_def, choice_wp_tc, pc_aux_wp]) 1) ]) ;

val _ = qed_goal "pcomp_choice_tc" Dtcm.thy 
  "pcomp_tc {B, choice_tc (insert A As)} = \
    \ choice_tc ((%a. pcomp_tc {B, a}) ` insert A As)"
  (fn _ => [ (rtac wp_tc_inj 1), (REPEAT (rtac ext 1)),
    (clarsimp_tac (cesimps [pcomp_wp_tc, choice_wp_tc, trm_choice_tc]) 1),
    Safe_tac, (TRYALL (etac lub_pt_mono' o decr)),
    (auto_tac (cesimps [choice_wp_tc])),
    (safe_tac (claset () addSss esimps [lub_pt_def, choice_wp_tc] 
      addSafter ("db", datac bspec 1))) ]) ;

val _ = qed_goalw "trm_or_prd_tc" Dtcm.thy 
  [prd_tc_def, wp_tc_def, mk_eq trm_alt, o_def] 
  "trm_tc S s | prd_tc s' S s" fn_at ;

val _ = qed_goal "prd_pcomp_tc" Dtcm.thy "prd_tc s' (pcomp_tc Cs) s = \
    \ (trm_tc (pcomp_tc Cs) s --> (ALL C:Cs. prd_tc s' C s))" 
  (fn _ => [ (clarsimp_tac (cesimps defs_tcm) 1), Safe_tac, Force_tac 2, 
    (etac allE 1), (etac disjE 1), (etac notE 2), (rtac refl 2),
    (dtac sym 1), Force_tac 1]) ;

val _ = qed_goal "prd_pcomp_tc2" Dtcm.thy "prd_tc s' (pcomp_tc {A, B}) s = \
    \ ((trm_tc B s --> prd_tc s' A s) & (trm_tc A s --> prd_tc s' B s))" 
  (fn _ => [ (simp_tac (esimps [prd_pcomp_tc, trm_pcomp_tc]) 1),
    Safe_tac, (ALLGOALS (rtac (trm_or_prd_tc RS disjE))), Auto_tac ]) ;

(* shorter proof later
val _ = qed_goalw "ref_tc_prdt" Dtcm.thy 
  [liftimp, o_def, ref_tc_def, prd_tc_def]
  "ref_tc A B = ((trm_tc A ---> trm_tc B) & \
    \ (ALL s'. prd_tc s' B ---> prd_tc s' A))"
  (fn _ => [Safe_tac,
    (force_tac (cesimps [trm_alt]) 1), Fast_tac 1, 
    (clarsimp_tac (cesimps defs_tcm) 1), 
    (eres_inst_tac [("x", "s")] allE 1 THEN etac impE 1), 
    Force_tac 1, (case_tac "B s" 1), Force_tac 1,
    (rtac exI 1), (rtac conjI 1), atac 2, Clarify_tac 1,
    (eres_inst_tac [("x", "s"), ("xa", "x")] allE2 1 THEN etac impE 1), 
    Force_tac 1, (etac allE 1), Safe_tac, contr_tac 2, Force_tac 1 ]) ;
*)

val _ = qed_goalw "prd_tc_imp_fis" Dtcm.thy [liftimp, prd_tc_def] 
  "prd_tc s' S ---> fis_tc S"
  (fn _ => [ Auto_tac, (rtac (fis_or_wp_tc RS disjE) 1), Auto_tac ]) ;

(* last result of section 10 of Abstract Commands paper *)
val _ = qed_goalw "wp_prd_tc" Dtcm.thy 
  [prd_tc_def, o_def, wp_tc_def, trm_tc_def, liftand]
  "wp_tc A Q s = (trm_tc A s & (ALL s'. prd_tc s' A s --> Q s'))"
  (fn _ => [ Safe_tac, (ALLGOALS Clarsimp_tac), Force_tac 1,
    (case_tac "A s" 1), contr_tac 1, 
    (rtac exI 1), (rtac conjI 1), atac 2, Clarify_tac 1,
    (etac allE 1), (etac mp 1), Force_tac 1 ]) ;

(* prop 7 of Dunne, A Theory of Generalised Substitutions. ZB2002 *) 
val _ = qed_goalw "ref_tc_prdt" Dtcm.thy [ref_tc_def]
  "ref_tc A B = ((trm_tc A ---> trm_tc B) & \
    \ (ALL s'. prd_tc s' B ---> prd_tc s' A))"
  (fn _ => [ (simp_tac (esimps [wp_prd_tc]) 1),
    Safe_tac, (rtac (trm_or_prd_tc RS disjE) 2), 
    (eres_inst_tac [("xa", "%s'. prd_tc s' A s")] allE2 2),
    (etac impE 2), (TRYALL Fast_tac) ]) ;

val _ = qed_goalw_spec_mp "pc_aux_ref_mono" Dtcm.thy [pc_aux_def, at_tc_def]
  "(ALL s:S. ref_tc (f s) (g s)) --> ref_tc (pc_aux (f ` S)) (pc_aux (g ` S))"
  (fn _ => [ Safe_tac, (rtac choice_tc_ref_mono 1), Safe_tac, 
    (rtac guard_tc_ref_mono 1), Auto_tac, 
    (force_tac (cds [ref_tc_prdt RS iffD1], esimps []) 1) ]) ;

val _ = qed_goalw_spec_mp "pcomp_tc_ref_mono" Dtcm.thy [pcomp_tc_alt]
  "(ALL s:S. ref_tc (f s) (g s)) --> \
    \ ref_tc (pcomp_tc (f ` S)) (pcomp_tc (g ` S))"
  (fn _ => [ Safe_tac, (rtac precon_tc_ref_mono 1), Auto_tac, 
    (force_tac (cds [ref_tc_prdt RS iffD1], esimps []) 1),
    (etac pc_aux_ref_mono 1) ]) ;

