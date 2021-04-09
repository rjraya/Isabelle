
structure Dtcr = struct val thy = theory "Dtcr" end ;
val _ = use_legacy_bindings Dtcr.thy ;

(** reachability, repetition, iteration, etc **)

AddIffs [treach.tr_0, breach.br_0] ;
AddSEs [reach_NT.I_0, icnt_tc.NTI] ;
val _ = bind_thm ("infch_of_tc_Suc", fold_rule [infch_of_tc_def] 
  ([infch_of_tc_def RS def_imp_eq RS fun_cong, nat_rec_Suc] MRS trans)) ;
Addsimps [infch_of_tc_Suc] ;

val [infchs_tc_coinduct, icnt_tc_coinduct] =
  map (rewrite_rule [mk_eq mem_Collect_eq] o
    read_instantiate [("X", "Collect ?P")]) 
  [infchs_tc.coinduct, icnt_tc.coinduct] ;

val _ = qed_goal_spec_mp "tr_Suc'" Dtcr.thy "sf : treach C s --> \
    \ C s0 = Term S --> s : S --> sf : treach C s0"
  (fn _ => [ (rtac impI 1), (etac treach.induct 1), Safe_tac,
    (ALLGOALS (rtac treach.tr_Suc)), Auto_tac ]) ;
  
val _ = qed_goal_spec_mp "br_Suc'" Dtcr.thy "sf : breach C s --> \
    \ C s = Term S --> s0 : S --> sf : breach C s0"
  (fn _ => [ (rtac impI 1), (etac breach.induct 1), Safe_tac,
    (ALLGOALS (rtac breach.br_Suc)), Auto_tac ]) ;
  
val _ = qed_goal "tr_br" Dtcr.thy "(sf : treach C si) = (si : breach C sf)"
  (fn _ => [ Safe_tac,
    (etac treach.induct 1), Fast_tac 1, (eatac br_Suc' 2 1),
    (etac breach.induct 1), Fast_tac 1, (eatac tr_Suc' 2 1) ]) ;

val treach_elim' = fold_rule [mk_eq tr_br] breach.elims ;
val breach_elim' = rewrite_rule [mk_eq tr_br] treach.elims ;
val treach_induct' = fold_rule [mk_eq tr_br] breach.induct ;
val breach_induct' = rewrite_rule [mk_eq tr_br] treach.induct ;

val _ = qed_goal "icnt_alt" Dtcr.thy "icnt_tc A = reach_NT A Un infchs_tc A"
  (fn _ => [ Safe_tac, 
    (etac reach_NT.induct 2),
    (TRYALL (eresolve_tac icnt_tc.intros THEN_ALL_NEW Fast_tac)),
    (etac icnt_tc.coinduct 2), (etac infchs_tc.elims 2), Fast_tac 2,
    (etac swap 1), (datac DiffI 1 1), (etac thin_rl 1), 
    (etac infchs_tc.coinduct 1), Safe_tac, 
    (etac icnt_tc.elims 1), (fast_tac (cis reach_NT.intros) 2),
    (REPEAT (rtac exI 1)), Safe_tac, (TRYALL (ares_tac [refl])),
    (rtac UnI1 1), Safe_tac, (etac notE 1),
    (eatac reach_NT.I_Suc 2 1) ]) ;

val _ = qed_goalw "rephat_all" Dtcr.thy 
  [repall_tc_def, rephat_def, mk_eq icnt_alt]
  "rephat C st = (if st : infchs_tc C then NonTerm else repall_tc C st)"
  (fn _ => [ Simp_tac 1 ]) ;

val _ = qed_goalw "rephat_all'" Dtcr.thy 
  [repall_tc_def, rephat_def, mk_eq icnt_alt]
  "rephat C st = (if st : icnt_tc C then NonTerm else repall_tc C st)"
  (fn _ => [ Simp_tac 1 ]) ;

val _ = qed_goalw_spec_mp "ic_isuc" Dtcr.thy [isuc_tc_def]
  "(s : infchs_tc A) --> (EX S. A s = Term S & isuc_tc A s : S) & \
    \ isuc_tc A s : infchs_tc A"
  (fn _ => [ (rtac impI 1), (etac infchs_tc.elims 1),
    (rtac someI 1), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "icn_ic" Dtcr.thy [infch_of_tc_def]
  "(s : infchs_tc A) --> (infch_of_tc A s n : infchs_tc A)"
  (fn _ => [ (rtac impI 1), (induct_tac "n" 1), Auto_tac, 
    (etac (ic_isuc RS conjunct2) 1) ]) ;

val _ = qed_goal_spec_mp "ic_chain" Dtcr.thy 
  "s : infchs_tc A --> (f = infch_of_tc A s --> \
    \ (EX S. A (f n) = Term S & f (Suc n) : S))"
  (fn _ => [ Safe_tac, (dtac icn_ic 1), (dtac ic_isuc 1), Force_tac 1 ]) ;

val _ = qed_goal_spec_mp "chain_ic" Dtcr.thy 
  "(ALL n. A (f n) = Term S & f (Suc n) : S) --> f m : infchs_tc A"
  (fn _ => [ (rtac impI 1), 
    (res_inst_tac [("X", "range f")] infchs_tc.coinduct 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "rep_tc" Dtcr.thy
  "ALL s. rep_tc (swap_tc o A) n s = swap_tc (rep n A s)" 
  (fn _ => [ (induct_tac "n" 1),
    (simp_tac (esimps [unitos_def, swap_tc_def, sts_of_ocs.defs]) 1),
    (clarsimp_tac (cesimps [rewrite_rule [o_def] seq_tc RS sym RS fun_cong]) 1),
    cong_tac 1, (rtac ext 1),
    (asm_full_simp_tac (esimps [o_def]) 1) ]) ;

val _ = qed_goal "rep_tc'" Dtcr.thy
  "rep_tc (swap_tc o A) n = swap_tc o rep n A" 
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [rep_tc]) 1) ]) ;

val _ = qed_goal "icnt_tc" Dtcr.thy "icnt_tc (swap_tc o A) = icnt A"
  (fn _ => [ Safe_tac, 
    (etac icnt.coinduct 1), (etac icnt_tc.elims 1),
    (force_tac (cesimps [swap_tc_Term_iff]) 1),
    (clarsimp_tac (cesimps [swap_tc_def]) 1),
    (etac icnt_tc.coinduct 1), (etac icnt.elims 1),
    (case_tac "swap_tc (A s)" 1), Force_tac 1,
    (force_tac (cesimps [swap_tc_Term_iff]) 1),
    (clarsimp_tac (cesimps [swap_tc_def]) 1) ]) ;
    
(*
val _ = qed_goalw "seq_tr" Dtcr.thy "seq_tc A (Term o treach A) "
*)

val ltacs = [ Safe_tac, 
  (REPEAT_FIRST (rtac image_eqI)), (TRYALL (ares_tac [refl])),
  (auto_tac (cesimps [rephat_def, repall_tc_def])) ] ;

val _ = qed_goal_spec_mp "repall_tc_Tlem" Dtcr.thy 
  "NonTerm ~: repall_tc A ` sa --> repall_tc A ` sa = Term ` treach A ` sa"
  (fn _ => ltacs) ;

val _ = qed_goal_spec_mp "rephat_Tlem" Dtcr.thy 
  "NonTerm ~: rephat A ` sa --> rephat A ` sa = Term ` treach A ` sa"
  (fn _ => ltacs) ;

val uss = esimps [prodtc_def] addsplits [split_if_asm] ;
val cuss = uss addsimps [choice_tc_def', Let_def] ;

val fptacs0 = [ (rtac ext 1), 
  (simp_tac (esimps [rephat_def, repall_tc_def, choice_tc_def', Let_def]) 1), 
  Safe_tac, (eresolve_tac [icnt_tc.elims, reach_NT.elims] 1),
  (asm_simp_tac (esimps [prodtc_def, seq_tc_def]) 2),
  (asm_simp_tac (esimps [prodtc_def, seq_tc_def]) 1),
  (force_tac (cesimps [rephat_def, repall_tc_def]) 1) ] ;

val fptacs1 = [
  (etac notE 1), (full_simp_tac (esimps [seq_tc_def']) 1),
  (case_tac "A x" 1), (eresolve_tac [reach_NT.I_0, icnt_tc.NTI] 1),
  (asm_full_simp_tac uss 1),
  (etac imageE 1), (eresolve_tac [reach_NT.I_Suc, icnt_tc.icI] 1), atac 1, 
  (full_simp_tac (esimps [rephat_def, repall_tc_def] 
      addsplits [split_if_asm]) 1) ] ;

val fptacs2 = [
  (asm_full_simp_tac (esimps [prodtc_def, sts_of_ocs.defs, seq_tc_def']) 1),
  (case_tac "A x" 1), (dresolve_tac [reach_NT.I_0, icnt_tc.NTI] 1),
  contr_tac 1, (asm_full_simp_tac uss 1),
  (dresolve_tac [repall_tc_Tlem, rephat_Tlem] 1),
  (Clarsimp_tac 1), Safe_tac, (eatac tr_Suc' 2 2),
  (etac treach_elim' 1), (ALLGOALS (rtac UnionI)), 
  Simp_tac 1, (rtac disjI2 1), rtac refl 1, Fast_tac 1,
  (ALLGOALS Clarsimp_tac), rtac refl 1, Fast_tac 1 ] ;

val _ = qed_goalw "rephat_isfp" Dtcr.thy [fprep_tc_def] "fprep_tc A (rephat A)"
  (fn _ => [ EVERY fptacs0, (case_tac "seq_tc A (rephat A) x" 1),
    EVERY fptacs1, EVERY fptacs2]) ;

(* converse doesn't hold, eg A = Y = (%s. Term UNIV) *)
val _ = qed_goalw_spec_mp "fprep_NT" Dtcr.thy [fprep_tc_def]
  "fprep_tc A Y --> Y s = NonTerm --> s : icnt_tc A"
  (fn _ => [ Safe_tac, (subgoal_tac "s : Y -` {NonTerm}" 1), Fast_tac 2,
    (etac icnt_tc.coinduct 1), (dres_inst_tac [("x", "z")] fun_cong 1),
    (full_simp_tac (uss addsimps [choice_tc_def, pext_tc_def, Let_def]) 1),
    Clarsimp_tac 2, (case_tac "A z" 1), Asm_simp_tac 1,
    (asm_full_simp_tac (uss addsimps [seq_tc_def']) 1), Force_tac 1 ]) ;

val _ = qed_goalw_spec_mp "fprep_NTr" Dtcr.thy [fprep_tc_def]
  "fprep_tc A Y --> s : reach_NT A --> Y s = NonTerm"
  (fn _ => [ Safe_tac, (etac reach_NT.induct 1), 
    (dres_inst_tac [("x", "s")] fun_cong 1),
    (asm_simp_tac cuss 1), (etac (seq_tc_NT RS sym) 1),
    (dres_inst_tac [("x", "s")] fun_cong 1),
    (asm_simp_tac (cuss addsimps [seq_tc_def']) 1), Force_tac 1 ]) ;

val _ = qed_goalw_spec_mp "fprep_T" Dtcr.thy [fprep_tc_def]
  "fprep_tc A Y --> x : treach A s --> (ALL S. Y s = Term S --> x : S)"
  (fn _ => [ (REPEAT (rtac impI 1)), (etac treach_induct' 1), 
    (dres_inst_tac [("x", "x")] fun_cong 1),
    (force_tac (claset (), cuss) 1),
    (dres_inst_tac [("x", "sf")] fun_cong 1), (case_tac "Y s" 1),
    (asm_full_simp_tac cuss 1),
    (etac notE 1), (rotate_tac ~1 1), (etac thin_rl 1),
    (force_tac (claset (), uss addsimps [seq_tc_def']) 1),
    Safe_tac, (etac allE 1), mp_tac 1,
    (asm_full_simp_tac cuss 1),
    hyp_subst_tac 1, (thin_tac "Y sf = ?Z" 1),
    (case_tac "seq_tc A Y sf" 1), Force_tac 1, (thin_tac "Not ?Z" 1), 
    (clarsimp_tac (claset (), uss addsimps [sts_of_ocs.defs, seq_tc_def']) 1),
    (rtac exI 1), (rtac conjI 1), (rtac disjI1 1), 
    (rtac refl 1), (rtac UnionI 1), atac 2, Force_tac 1 ]) ;

val _ = qed_goalw_spec_mp "fprep_T2'" Dtcr.thy [fprep_tc_def]
  "fprep_tc A Y --> s : {s'. EX S. Y s' = Term S & x : S & \
    \ x ~: treach A s'} --> s : icnt_tc A"
  (fn _ => [ (REPEAT (rtac impI 1)), (etac icnt_tc.coinduct 1), 
    (Clarsimp_tac 1), (case_tac "A z" 1), Force_tac 1,
    (rtac exI 1), (rtac conjI 1), atac 1, 
    (dres_inst_tac [("x", "z")] fun_cong 1),
    (case_tac "seq_tc A Y z" 1),
    (asm_full_simp_tac cuss 1),
    (clarsimp_tac (claset (), cuss addsimps [Union_def, sts_of_ocs.defs,
      seq_tc_def']) 1), Safe_tac,
    (rtac exI 1), (rtac conjI 1), atac 1, (rtac disjI1 1),
    (rtac exI 1), Safe_tac, (TRYALL (atac ORELSE' etac sym)),
    (etac notE 1), (eatac tr_Suc' 2 1) ]) ;

val fprep_T2 = tacsthm 
  [Simp_tac 2, rtac exI 2, (REPEAT_SOME (rtac conjI)) ] fprep_T2' ;

val _ = qed_goalw_spec_mp "rephat_is_lfp" Dtcr.thy [ref_tc_alt, rephat_def]
  "fprep_tc A Y --> ref_tc (rephat A) Y"
  (fn _ => [ Safe_tac, (asm_full_simp_tac uss 1),
    (case_tac "Y s" 1), (datac fprep_NT 1 1), contr_tac 1,
    (rtac exI 1), (rtac conjI 1), atac 2, Safe_tac,
    (etac swap 1), (eatac fprep_T2 3 1) ]) ;

val _ = qed_goalw "repall_tc_isfp" Dtcr.thy [fprep_tc_def] 
  "fprep_tc A (repall_tc A)"
  (fn _ => [ EVERY fptacs0, (case_tac "seq_tc A (repall_tc A) x" 1),
    EVERY fptacs1, EVERY fptacs2]) ;

val _ = qed_goalw_spec_mp "repall_tc_is_gfp" Dtcr.thy 
  [ref_tc_alt2, repall_tc_def] "fprep_tc A Y --> ref_tc Y (repall_tc A)"
  (fn _ => [ Safe_tac, Simp_tac 1, (rtac conjI 1), 
    (etac contrapos_nn 1), (eatac fprep_NTr 1 1),
    Safe_tac, (case_tac "Y s" 1), contr_tac 1,
    (rtac exI 1), (rtac conjI 1), atac 2, Safe_tac,
    (eatac fprep_T 2 1) ]) ;

val _ = qed_goal "scrl1" Dtcr.thy 
  "choice_tc Cs ` S = prodtc ` (%s. Let s ` Cs) ` S"
  (fn _ => [ (auto_tac (cesimps [choice_tc_def'])) ]) ;

val _ = qed_goal_spec_mp "scrl2" Dtcr.thy 
  "A x = Term S --> Let x o seq_tc A = prodtc o (%C. C ` S)"
  (fn _ => [ Safe_tac, (rtac ext 1),
    (asm_simp_tac (esimps [Let_def, seq_tc_def']) 1) ]) ;

val _ = qed_goal "scrl3" Dtcr.thy "Let s o choice_tc = prodtc o image (Let s)"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [choice_tc_def', Let_def]) 1) ]) ;

val _ = qed_goal "ch_ch" Dtcr.thy 
  "choice_tc o image choice_tc = choice_tc o Union"
  (fn _ => [ (REPEAT (rtac ext 1)), 
    (simp_tac (esimps [choice_tc_def]) 1),
    (simp_tac (esimps ([mk_ap pext_pext, mk_ap pextomap] RL [sym])) 1),
    (cong_tac 1), (rtac ext 1),
    (simp_tac (esimps [choice_tc_def, Let_def]) 1) ]) ;

(*
val _ = qed_goal "ch_ch" Dtcr.thy 
  "choice_tc o image choice_tc = choice_tc o Union"
  (fn _ => [ (REPEAT (rtac ext 1)), 
    (simp_tac (esimps [choice_tc_def']) 1),
    (simp_tac (esimps [scrl3, image_compose RS sym]) 1),
    (simp_tac (esimps [image_compose, pext_prod']) 1),
    (Conv.CONV_TAC (SOME o eta_conversion : conv)),
    (cong_tac 1), (force_tac (cesimps [Let_def]) 1) ]) ;
*)

val _ = qed_goal "seq_choice_tcL" Dtcr.thy 
  "seq_tc (choice_tc Cs) B = choice_tc ((%C. seq_tc C B) ` Cs)"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [seq_tc_def, choice_tc_def]) 1),
    (simp_tac (esimps ([mk_ap pext_tc_fun, mk_ap pextomap] RL [sym])) 1),
    cong_tac 1, (rtac ext 1), (simp_tac (esimps [Let_def]) 1) ]) ;

val _ = qed_goal_spec_mp "seq_choice_tcR" Dtcr.thy 
  "cs ~= {} --> seq_tc A (choice_tc cs) = choice_tc (seq_tc A ` cs)"
  (fn _ => [ (rtac impI 1), (rtac ext 1), (case_tac "A x" 1), 
    (asm_simp_tac (esimps [seq_tc_def', choice_tc_def', prodtc_def]) 1),
    (etac nonemptyE 1), (REPEAT_ALL_NEW (ares_tac [image_eqI, refl]) 1),
    (asm_simp_tac (esimps [Let_def, seq_tc_def']) 1),
    (asm_simp_tac (esimps [choice_tc_def', seq_tc_def']) 1),
    (asm_simp_tac (esimps [image_compose RS sym, scrl2]) 1),
    (asm_simp_tac (esimps [scrl1, image_compose, pext_prod']) 1),
    (cong_tac 1), (force_tac (cesimps [Let_def]) 1) ]) ;

(* characterisation of repall *)
val _ = qed_goalw "crn_isfp" Dtcr.thy [fprep_tc_def]
  "fprep_tc C (choice_tc (rep_tc C ` UNIV))"
  (fn _ => [ (rtac ext 1),
    (subgoal_tac "{choice_tc (seq_tc C ` range (rep_tc C)), unit_tc} = \
      \ choice_tc ` {seq_tc C ` range (rep_tc C), {unit_tc}}" 1),
    Simp_tac 2, (simp_tac (esimps [seq_choice_tcR]) 1),
    (asm_simp_tac (HOL_ss addsimps [mk_ap ch_ch]) 1),
    (etac thin_rl 1), (cong_tac 1), Safe_tac, 
    ((case_tac "xb" THEN_ALL_NEW Force_tac) 1),
    (ALLGOALS (rtac image_eqI)), (rtac (rep_tc.rep_tc_0 RS sym) 3),
    (rtac (rep_tc.rep_tc_Suc RS sym) 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "rep_tc_n_NT" Dtcr.thy 
  "ALL s. rep_tc C n s = NonTerm --> s : reach_NT C"
  (fn _ => [ (induct_tac "n" 1), ALLGOALS Clarsimp_tac, 
    (case_tac "C s" 1), (Clarsimp_tac 1),
    (asm_full_simp_tac (uss addsimps [seq_tc_def']) 1),
    Clarify_tac 1, (etac allE 1), (etac impE 1), (etac sym 1),
    (eatac reach_NT.I_Suc 2 1) ]) ;

val _ = qed_goal_spec_mp "rep_tc_n_T" Dtcr.thy 
  "ALL s S. rep_tc C n s = Term S --> S <= treach C s"
  (fn _ => [ (induct_tac "n" 1), ALLGOALS Clarsimp_tac, 
    (case_tac "C s" 1), 
    (ALLGOALS (asm_full_simp_tac (uss addsimps [seq_tc_def']))),
    Clarify_tac 1, (etac allE2 1), (etac impE 1), (etac sym 1),
    (datac subsetD 1 1), (eatac tr_Suc' 2 1) ]) ;

val _ = qed_goal "repall_tc_alt" Dtcr.thy
  "repall_tc C = choice_tc (rep_tc C ` UNIV)"
  (fn _ => [ (rtac ref_tc_antisym 1),
    (rtac repall_tc_is_gfp 2), (rtac crn_isfp 2),
    (simp_tac (esimps [repall_tc_def, ref_tc_alt]) 1),
    (simp_tac cuss 1), Safe_tac, rewtac Let_def, 
    (etac (sym RS rep_tc_n_NT) 1), 
    (dtac (sym RS rep_tc_n_T) 1), Fast_tac 1 ]) ;

val _ = qed_goal "repall_tc" Dtcr.thy 
  "repall_tc (swap_tc o C) s = swap_tc (repall C s)"
  (fn _ => [
    (simp_tac (esimps [repall_def', repall_tc_alt]) 1),
    (simp_tac (esimps [rewrite_rule [o_def] choice_tc RS sym RS fun_cong]) 1),
    cong_tac 1, (rtac set_ext 1),
    (auto_tac (cesimps [image_iff, rep_tc'])) ]) ;

val _ = qed_goal "rephat_star" Dtcr.thy 
  "rephat (swap_tc o C) s = swap_tc (repstar C s)"
  (fn _ => [ (auto_tac (cesimps 
      [repstar_def'', rephat_all', icnt_tc, repall_tc])) ]) ;

(** intuitive if, while **)

val _ = qed_goalw "if_tc_prog" Dtcr.thy 
  [if_tc_def, choice_tc_def', prodtc_def]
  "if_tc G A B s = (if G s then A s else B s)"
  (fn _ => [ (auto_tac (cesimps [Let_def, guard_tc_def])),
    (ALLGOALS (case_tac "A s")), (ALLGOALS (case_tac "B s")), Auto_tac ]) ;

val _ = qed_goalw "ifthen_tc_prog" Dtcr.thy 
  [ifthen_tc_def, choice_tc_def', prodtc_def]
  "ifthen_tc G A s = (if G s then A s else Term {s})"
  (fn _ => [ (auto_tac (cesimps [Let_def, guard_tc_def])),
    (case_tac "A s" 1), Auto_tac ]) ;

val _ = bind_thm ("rephat_seq", rewrite_rule [fprep_tc_def] rephat_isfp) ;

val _ = qed_goalw "while_tc_prog" Dtcr.thy [while_tc_def, ifthen_tc_def] 
  "while_tc G A = ifthen_tc G (seq_tc A (while_tc G A))"
  (fn _ => [
    let val th = rephat_seq RS arg_cong RS trans ;
    in (res_inst_tac [("f1", "%x. seq_tc x ?y")] th 1) end,
    (rewrite_tac (map mk_eq [Xguard_tc RS sym, seq_tc_assoc, seq_choice_tcL])),
    (Simp_tac 1)]) ;

val _ = qed_goal_spec_mp "icnt_tc_ref_mono" Dtcr.thy 
  "ref_tc A B --> s : icnt_tc B --> s : icnt_tc A"
  (fn _ => [ Safe_tac, (etac icnt_tc.coinduct 1),
    (case_tac "A z" 1), Force_tac 1,
    (datac ref_tc_TermD 1 1), Clarify_tac 1,
    (etac icnt_tc.elims 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "reach_NT_ref_mono" Dtcr.thy 
  "ref_tc A B --> s : reach_NT B --> s : reach_NT A"
  (fn _ => [ Safe_tac, (etac reach_NT.induct 1),
    (datac ref_tc_NonTermD 1 1), Fast_tac 1,
    (case_tac "A s" 1), Fast_tac 1,
    (datac ref_tc_TermD 1 1), Clarify_tac 1,
    (etac reach_NT.I_Suc 1), Auto_tac ]) ;

val _ = qed_goal_spec_mp "breach_ref_mono'" Dtcr.thy 
  "ref_tc A B --> s : breach B x --> s ~: reach_NT A --> s : breach A x"
  (fn _ => [ (rtac impI 1), (rtac impI 1),
    (etac breach.induct 1), Fast_tac 1, Clarify_tac 1,
    (case_tac "A sf" 1), (fast_tac (ces [notE]) 1),
    (datac ref_tc_TermD 1 1), Clarsimp_tac 1, 
    (datac subsetD 1 1), (etac impE 1), 
    (eatac breach.br_Suc 2 2), (etac contrapos_nn 1),
    (eatac reach_NT.I_Suc 2 1) ]) ; 

val _ = qed_goal_spec_mp "treach_ref_mono" Dtcr.thy
  "ref_tc A B --> s ~: reach_NT A --> treach B s <= treach A s"
  (fn _ => [ (clarsimp_tac (cesimps [tr_br]) 1), 
    (eatac breach_ref_mono' 2 1) ]) ; 

val _ = qed_goal_spec_mp "repall_tc_ref_mono" Dtcr.thy 
  "ref_tc A B --> ref_tc (repall_tc A) (repall_tc B)"
  (fn _ => [ (rtac impI 1), 
    (simp_tac (esimps [ref_tc_def', wp_tc_def, repall_tc_def]) 1),
    Safe_tac, (datac reach_NT_ref_mono 1 1), (contr_tac 1),
    (datac treach_ref_mono 1 1), (Force_tac 1) ]) ;

val _ = qed_goal_spec_mp "rephat_ref_mono" Dtcr.thy 
  "ref_tc A B --> ref_tc (rephat A) (rephat B)"
  (fn _ => [ (rtac impI 1), 
    (simp_tac (esimps [ref_tc_def', wp_tc_def, rephat_def]) 1),
    Safe_tac, (datac icnt_tc_ref_mono 1 1 THEN contr_tac 1),
    (clarsimp_tac (cesimps [icnt_alt]) 1),
    (datac treach_ref_mono 1 1), (Force_tac 1) ]) ;

val _ = qed_goal "rephat_magic" Dtcr.thy "rephat magic_tc = unit_tc"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [rephat_def, magic_tc_def]) 1),
    Safe_tac, (etac treach.elims 2),
    (etac icnt_tc.elims 1), (auto_tac (cesimps [magic_tc_def])) ]) ;

val _ = qed_goal "rephat_skip" Dtcr.thy "rephat unit_tc = abort_tc"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [rephat_def, abort_tc_def]) 1),
    (rtac (UNIV_I RS icnt_tc.coinduct) 1), Force_tac 1 ]) ;



