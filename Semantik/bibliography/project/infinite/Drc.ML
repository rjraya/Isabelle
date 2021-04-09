
structure Drc = struct val thy = theory "Drc" end ;
val _ = use_legacy_bindings Drc.thy ;

(** lemmas and theorems to do with repetitive closure **)

fun utr() = update_thy "Drc" ;
fun utor() = update_thy_only "Drc" ;
fun ur() = use "Drc.ML" ;

val _ = qed_goal "wr_repall" Drc.thy "wreach C = repall C"
  (fn _ => [ rtac ext 1, rewtac repall_def, rtac equalityI 1,
    rtac UN_least 2, (Full_simp_tac 2),
    (induct_tac "n" 2), 
    (rewtac (mk_eq rep_Suc')), 
    (rtac subset_trans 3), (rtac wr_seq 4),
    (rewrite_goals_tac [seq_def, extos_def]),
    rtac subsetI 1, etac wreach.induct 1, etac UN_E 2, 
    (res_inst_tac [("a", "Suc n")] UN_I 2), 
    (rewtac (mk_eq rep_Suc')), rtac seqIT 3, 
    (res_inst_tac [("a", "0")] UN_I 1), 
    (auto_tac (cesimps [unitos_def]))]) ;

structure repall = struct
  fun rwwr th = rewrite_rule (map mk_eq [wr_repall, wreach_rel])
    (transfer Drc.thy th) ; 
  val intrs as [rep0, rep1AI, repA1I] =
    map rwwr [wreach.wr_0, wrrel.wr_Suc, refl RSN (2, wreach.wr_Suc)] ;
  val rep1I = rep0 RSN (2, repA1I) ;
  end ;

val _ = qed_goal "rep_plus" Drc.thy
  "rep (m + n) A = seq (rep m A) (rep n A)"
  (fn _ => [(induct_tac "m" 1), Simp_tac 1,
    Asm_simp_tac 1, rtac seq_assoc 1]) ;
    
val _ = qed_goal "rep_times" Drc.thy
  "rep (m * n) A = rep m (rep n A)"
  (fn _ => [(induct_tac "m" 1), Simp_tac 1,
    (asm_simp_tac (esimps [rep_plus]) 1)]) ;

val _ = qed_goal "repall_def'" Drc.thy
  "repall C = choice (range (%n. rep n C))"
  (fn _ => [ rtac ext 1, 
    (rewrite_goals_tac [choice_def, repall_def]), Simp_tac 1]) ;

val _ = qed_goal "repstar_def'" Drc.thy 
  "repstar C = choice {repall C, guard (infch C) abort}"
  (fn _ => [rtac ext 1, 
    (auto_tac (cesimps [repstar_def, abort_def, guard_def, choice_def]))]) ;

val _ = qed_goalw_spec_mp "repall_repstar" Drc.thy [repstar_def]
  "x : repall C s --> x : repstar C s" fn_at ;

val _ = qed_goal_spec_mp "repall_term" Drc.thy 
  "(ALL st. NonTerm ~: A st) --> (ALL st. NonTerm ~: repall A st)"
  (fn _ => [ (rewtac (mk_eq (wr_repall RS sym))), Clarify_tac 1,
    (etac wreach.elims 1), Auto_tac ]) ;

val _ = qed_goal "loop_abort" Drc.thy "loop = abort"
  (fn _ => [rtac ext 1, 
    (rewrite_goals_tac [loop_def, while_def, abort_def]), 
    Safe_tac, (rtac seqINT 2), 
    (simp_tac (esimps 
      [repstar_def', abort_def, choice_def, guard_def, infch_skip]) 2),
    (eatac seqE 1 1), (full_simp_tac (esimps [guard_def]) 1)]) ;

val _ = qed_goal "seq_repall" Drc.thy
  "seq (repall C) C = seq C (repall C)"
  (fn _ => [ (simp_tac (esimps [wr_repall RS sym, seq_wr]) 1) ]) ;

val _ = qed_goalw "Term_star" Drc.thy [repstar_def]
  "(Term ns : repstar C s) = (Term ns : repall C s)" fn_at ;

val _ = qed_goalw_spec_mp "repstar_nt" Drc.thy 
  [repstar_def, infch_s, mk_eq (wr_repall RS sym)]
  "(NonTerm : repstar A s) = (s : icnt A)"
  (fn _ => [ (auto_tac (cesimps [icnt_chs_wr, wreach_rel RS sym])) ]) ;

val _ = qed_goal_spec_mp "repstar_seq_nt" Drc.thy 
  "(NonTerm : repstar A s) = (NonTerm : seq A (repstar A) s)"
  (fn _ => [ (auto_tac (ces (seqE :: icnt.intros), esimps [repstar_nt])),
    (etac icnt.elims 1), 
    (auto_tac (ces seq.intros, esimps [repstar_nt RS sym])) ]) ;

val _ = qed_goal_spec_mp "seq_repstar_le" Drc.thy 
  "seq (repstar A) A s <= repstar A s"
  (fn _ => [ (safe_tac (ces [seqE])), 
    (full_simp_tac (esimps [Term_star, wr_repall RS sym]) 1),
    (datac (refl RSN (2, wreach.wr_Suc)) 1 1),
    (force_tac (cesimps [repstar_def, wr_repall]) 1) ]) ;

val ssiga = esimps [infch_s, guard_def, abort_def] addsplits [split_if_asm] ;

val _ = qed_goal "repstar_lem" Drc.thy
  "guard (infch C) abort st <= seq C (guard (infch C) abort) st"
  (fn _ => [ (Safe_tac), (full_simp_tac ssiga 1),
    (etac infchs.elims 1), Safe_tac, (etac seqIT 1),
    (asm_simp_tac (esimps [infch_s, guard_def, abort_def]) 1) ]) ;

val _ = qed_goal "repstar_def''" Drc.thy
  "repstar C s = repall C s Un (if s : icnt C then {NonTerm} else {})"
  (fn _ => [ (rtac set_ext 1), (case_tac "x" 1),
    (safe_tac (ces [repall_repstar])),
    (auto_tac (claset (),
      esimps [repstar_nt, Term_star] addsplits [split_if_asm])) ]) ;

val _ = qed_goal "repstar_choice" Drc.thy
  "repstar C = choice {repall C, %s. if s : icnt C then {NonTerm} else {}}"
  (fn _ => [ (rtac ext 1),
    (simp_tac (esimps [repstar_def'', choice_def]) 1) ]) ;

val _ = qed_goal "seq_repstar" Drc.thy
  "seq (repstar C) C = seq C (repstar C)"
  (fn _ => [ (simp_tac (esimps 
      [repstar_choice, seq_choiceR, seq_choiceL, seq_repall]) 1),
    rtac ext 1, rewtac choice_def, Auto_tac,
    (ALLGOALS (etac notE)), 
    (auto_tac (ces [seqE], simpset () addsplits [split_if_asm])),
    (dtac icnt.NTI 2), (datac icnt.icI 1 3),
    (etac icnt.elims 1), Safe_tac, (etac seqIT 1), 
    (TRYALL (rtac seqINT)), Auto_tac ]) ;

val _ = qed_goal "seq_repstar" Drc.thy
  "seq (repstar C) C = seq C (repstar C)"
  (fn _ => [ (simp_tac (esimps 
      [repstar_def', seq_choiceR, seq_choiceL, seq_repall]) 1),
    rtac ext 1, rewtac choice_def, Safe_tac,
    Fast_tac 1, Fast_tac 2, 
    (full_simp_tac (esimps [gia_seq]) 1),
    (dtac (repstar_lem RS subsetD) 1), (etac disjI2 1),
    (safe_tac (ces [seqE])), Simp_tac 1, (rtac disjI1 1), (etac seqINT 1), 
    (full_simp_tac ssiga 1),
    (rtac disjI2 1), (datac infchs.I 1 1), hyp_subst_tac 1, (rtac seqINT 1),
    (simp_tac ssiga 1) ]) ;

(* note - cannot simplify using repall_seq or repstar_seq as it would loop *)
val _ = qed_goalw "repall_seq" Drc.thy [mk_eq (wr_repall RS sym)]
  "repall C = choice {seq C (repall C), unitos}" (fn _ => [(rtac wr_chr 1)]) ;
  
val _ = qed_goal "repstar_seq" Drc.thy 
  "repstar C = choice {seq C (repstar C), unitos}"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [repstar_def', seq_choiceR, choice_def,
      repall_seq RS fun_cong]) 1), 
    Safe_tac, (dtac (repstar_lem RS subsetD) 1), contr_tac 1, 
    (etac seqE 1), (fast_tac (cis [seqINT]) 1), 
    (asm_full_simp_tac ssiga 1),
    (datac infchs.I 1 1), contr_tac 1 ]) ;

val _ = qed_goal "repall_seq_le" Drc.thy 
  "seq C (repall C) state <= repall C state"
  (fn _ => [ (force_tac (cesimps [choice_def, repall_seq RS fun_cong]) 1) ]) ;

val _ = qed_goal "repstar_seq_le" Drc.thy 
  "seq C (repstar C) state <= repstar C state"
  (fn _ => [ (force_tac (cesimps [choice_def, repstar_seq RS fun_cong]) 1) ]) ;

val _ = qed_goal "repI0" Drc.thy 
  "Term state : rep 0 C state" 
  (fn _ => [(simp_tac (esimps [unitos_def]) 1)]) ;

val _ = qed_goal "repallI0" Drc.thy 
  "Term state : repall C state" (fn _ => [ (resolve_tac repall.intrs 1)]) ;

AddSIs [repI0, repallI0] ;

val _ = qed_goal "repI1" Drc.thy 
  "rep 1 C = C" (fn _ => [Simp_tac 1]) ;

val _ = qed_goal "repallI1" Drc.thy 
  "C state <= repall C state"
  (fn _ => [ (safe_tac (ces [repall.rwwr wrrel.wr1])) ]) ;

val fprep_alt = rewrite_rule [fprepst_def] fprep_def ;

val _ = qed_goalw "fprep_alt2" Drc.thy [fprep_alt, mk_eq fun_cong_all]
  "fprep A X = (X = choice {seq A X, unitos})" ft_mc ;

(* any fixpoint contains repall, ie gencref X (repall A) *)
val _ = qed_goalw_spec_mp "repall_is_gfp" Drc.thy [gencref_alt, fprep_alt]
  "fprep A X --> gencref X (repall A)"
  (fn _ => [ Safe_tac, 
    (etac (repall.rwwr wrrel.induct) 1), (ALLGOALS Asm_simp_tac),
    (ALLGOALS (rtac disjI2)), (case_tac "cr" 2),
    (auto_tac (ces [seqIT, seqINT], simpset ()))]) ;

val fpra = rewrite_rule [gencref_alt] repall_is_gfp RS spec ;

(* if a fixpoint contains Term st outside repall, then infch holds *)
val _ = qed_goalw_spec_mp "oracic" Drc.thy [infch_s, fprep_alt]
  "fprep A X & cr : X state - repall A state --> infch A state"
  (fn _ => [ rtac impI 1, (etac conjE 1), 
    (chop_tac 1 (etac infchs_coinduct 1)),
    Asm_full_simp_tac 1, (safe_tac (ces [seqE])), 
    (dtac repall.rep1I 1), contr_tac 1,
    (rtac exI 1), Safe_tac, 
    (datac repall.rep1AI 1 3), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "oracic_NT" Drc.thy [mk_eq totceqv_alt]
  "totceqv X (choice {seq A X, unitos}) & \
    \ NonTerm : X state - repall A state --> state : infchs A"
  (fn _ => [ rtac impI 1, (etac conjE 1),
    (chop_tac 1 (etac infchs_coinduct 1)),
    (full_simp_tac (esimps [choice_def, unitos_def]) 1), 
    (eres_inst_tac [("x", "z")] allE 1),
    (safe_tac (ces [seqE] addSss (esimps []))), 
    (TRYALL (dtac repall.rep1I THEN' contr_tac)),
    (REPEAT (EVERY [ (rtac exI 1), Safe_tac, atac 1, atac 1,
      (datac repall.rep1AI 1 1), contr_tac 1 ])) ]) ;

val _ = qed_goal_spec_mp "oracic_tc" Drc.thy 
  "totceqv X (choice {seq A X, unitos}) & \
    \ (cr : X state - repall A state & NonTerm ~: repall A state) --> \
    \ state : infchs A"
  (fn _ => [ rtac impI 1, (etac conjE 1),
    (chop_tac 1 (etac infchs_coinduct 1)),
    (ftac (totceqv_alt RS defD1) 1),
    (full_simp_tac (esimps [choice_def, unitos_def]) 1), 
    (eres_inst_tac [("x", "z")] allE 1),
    (safe_tac (ces [seqE] addSss (esimps []))), 
    (TRYALL (dtac repall.rep1I THEN' contr_tac)),
    (rtac exI 1), Safe_tac, atac 1, atac 1,
    (REPEAT ((datac repall.rep1AI 1 1) THEN contr_tac 1)),
    (dtac (conjI RS oracic_NT) 1), Fast_tac 1,
    (etac infchs.elims 1), Fast_tac 1 ]) ;

(* cmdMng (repall cmA) is a fixed point of X = (A ; X) [] Skip *)
(* thus repall is gfp under gencref ordering *)
val _ = qed_goalw "repall_isfp" Drc.thy [fprep_alt] "fprep A (repall A)"
  (fn _ => [ (simp_tac (esimps [wr_repall RS sym, wr_chr']) 1) ]) ;

val _ = qed_goalw "repall_isfp" Drc.thy [fprep_alt] "fprep A (repall A)"
  (fn _ => [ (rtac allI 1), (rtac trans 1), 
    (rtac (repall_seq RS fun_cong) 1),
    (simp_tac (esimps [choice_def, unitos_def]) 1) ]) ;

val repall_isfp_st = rewrite_rule [fprep_def] repall_isfp RS spec ;

val _ = qed_goalw_spec_mp "extfp_infch_alt" Drc.thy [fprepst_def]
  "Y = choice {X, %st. if st : infchs A then {NonTerm} else {}} --> \
    \ fprepst A X state --> fprepst A Y state"
  (fn _ => [ Safe_tac, 
    (ALLGOALS (clarsimp_tac (claset (),
      esimps [choice_def, seq_choiceR] addsplits [split_if_asm]))), 
    Safe_tac, (safe_tac (ces [seqE])),
    (ALLGOALS (clarsimp_tac (claset (),
      esimps [] addsplits [split_if_asm]))), 
    (etac notE 2 THEN etac seqINT 2),
    (etac notE 2 THEN eatac infchs.I 1 2),
    (etac infchs.elims 1), (etac notE 1), (etac notE 1),
    (rtac seqIT 1), Auto_tac ]) ;

(*
val _ = qed_goalw_spec_mp "extfp_infch_alt" Drc.thy [fprepst_def]
  "Y = choice {X, %st. if st : infchs A then {NonTerm} else {}} --> \
    \ fprepst A X state --> fprepst A Y state"
  (fn _ => [ Safe_tac, 
    (ALLGOALS (clarsimp_tac (claset (),
      esimps [choice_def, seq_choiceR] addsplits [split_if_asm]))), 
    Safe_tac,
    
    (etac seqE 2), Fast_tac 2, 
    (force_tac (claset (), simpset () addsplits [split_if_asm]) 2), 

    (etac thin_rl 1), (etac infchs.elims 1), (etac thin_rl 1),
    (etac notE 1), (rtac seqIT 1), Fast_tac 1, Simp_tac 1,

    (etac seqE 1), (fast_tac (cis [seqINT]) 1), 
    (clarsimp_tac (claset (), simpset () addsplits [split_if_asm]) 1), 
    (etac notE 1 THEN eatac infchs.I 1 1) ]) ;
*)

val _ = qed_goalw_spec_mp "extfp_infch" Drc.thy [infch_s]
  "(ALL state. \
    \ Y state = X state Un (if infch A state then {NonTerm} else {})) --> \
    \ fprepst A X state --> fprepst A Y state"
  (fn _ => [ Safe_tac, (rtac extfp_infch_alt 1), atac 2, 
    (rtac ext 1), (auto_tac (cesimps [choice_def])) ]) ;

(* A* is a fixed point of X = (A ; X) [] Skip *)

val _ = qed_goalw "repstar_isfp" Drc.thy [fprep_def] "fprep A (repstar A)"
  (fn _ => [ rtac allI 1, rtac extfp_infch 1, rtac repall_isfp_st 2,
    rewtac (mk_eq repstar_def), Fast_tac 1]) ;

val _ = qed_goalw "repstar_isfp" Drc.thy [fprep_alt] "fprep A (repstar A)"
  (fn _ => [ (rtac allI 1), (rtac trans 1), 
    (rtac (repstar_seq RS fun_cong) 1),
    (simp_tac (esimps [choice_def, unitos_def]) 1) ]) ;

val _ = qed_goalw_spec_mp "repstar_is_lfp" Drc.thy
  (egMil_def :: repstar_def :: map mk_eq [totcref_alt, partcref_alt]) 
  "fprep A Y --> egMil (repstar A) Y"
  (fn _ => [Safe_tac, (datac (fpra RS subsetD) 1 2), 
    (full_simp_tac (HOL_ss addsplits [split_if_asm]) 3),
    (REPEAT (Fast_tac 2)), (rtac (notI RS notnotD) 1),
    (dtac (conjI RS oracic) 1), Fast_tac 1, Asm_full_simp_tac 1]) ;

(* in the generalised substitutions context, where generalised substitutions
  which are equivalent in terms of total correctness refinement are regarded
  as the same, also want repstar to be an lfp *)

val _ = qed_goalw_spec_mp "repstar_is_tc_lfp" Drc.thy [mk_eq totcref_alt]
  "totceqv X (choice {seq A X, unitos}) --> totcref (repstar A) X"
  (fn _ => [ (Clarify_tac 1),
    (rtac (notI RS notnotD) 1),
    (dtac (conjI RS oracic_tc) 1), Safe_tac, atac 1, 
    (auto_tac (cesimps [repstar_def, infch_s])) ]) ;
  
(* wlp and termination conditions for repstar *)

val _ = qed_goalw "wlpm_repstar" Drc.thy [wlpm_def, repstar_def, repall_def]
  "wlpm (repstar A) Q state = (ALL n. wlpm (rep n A) Q state)"
  (fn _ => [Auto_tac]) ;

val _ = qed_goalw "trmm_repstar" Drc.thy 
  [trmm_def, saf_def, repstar_def, repall_def]
  "trmm (repstar A) state = (saf A state & ~ infch A state)"
  (fn _ => [Auto_tac]) ;

val _ = qed_goal "wlpca" Drc.thy 
  "wlpm (repstar A) = wlpm (repall A)"
  (fn _ => [(REPEAT (rtac ext 1)), 
    (rewrite_goals_tac [repstar_def, wlpm_def]), Auto_tac]) ;

val _ = map store_thm [ ("oracic", oracic), ("extfp_infch", extfp_infch)] ;

(** fixpoint formulation of wlpm (repstar A) Q,
  as in Steve's email of 28 Aug 2001;
  note - this is least (weakest) fixpoint of conditions, nothing to do 
  with the Egli-Milner stuff above;
  wlp (A*, Q) = lfp of Y = wlp (A, Y) & Q **)

(* wlpm (repstar A) Q is a fixpoint *)

val _ = qed_goalw "wrfp" Drc.thy [Let_def]
  "let wlpstar = wlpm (repstar A) Q \
    \ in wlpstar = (wlpm A wlpstar && Q)"
  (fn _ => [rtac ext 1, 
    (simp_tac (esimps [wlpca, seq_wlp RS sym]) 1),
    (* must simplify only LHS using repall_seq,
      and cannot use simp_tac for repall_seq as this would loop *)
    let val ac' = read_instantiate_sg (sign_of Dmng.thy) 
	[("f", "wlpm")] arg_cong ;
    in (simp_tac (esimps [(repall_seq RS ac'), choice_wlp]) 1) end]) ;

val _ = qed_goal_spec_mp "wrwfp_lem" Drc.thy 
  "(Y ---> wlpm A Y && Q) --> Y s --> tn : wreach A s --> \
    \ (ALL nst. tn = Term nst --> Y nst)"
  (fn _ => [ (rtac impI 1), (rtac impI 1),  (rtac impI 1), 
    (full_simp_tac (esimps [wlpm_def, mk_eq (wr_repall RS sym)]) 1),
    (etac wreach.induct 1), TRYALL Fast_tac ]) ;

val _ = qed_goal_spec_mp "wrwfp_all" Drc.thy 
  "(Y ---> wlpm A Y && Q) --> (Y ---> wlpm (repall A) Q)"
  (fn _ => [ (rtac impI 1),
    (simp_tac (esimps [wlpm_def, mk_eq (wr_repall RS sym) ]) 1), 
    (Clarify_tac 1), (fatac (refl RSN (4, wrwfp_lem)) 2 1),
    (full_simp_tac (esimps [wlpm_def]) 1), Fast_tac 1 ]) ;

val _ = bind_thm ("wrwfp'", fold_rule [mk_eq wlpca] wrwfp_all) ;
(* any other fixpoint is stronger *)
val _ = bind_thm ("wrwfp", liftimp_refl' RS wrwfp') ;

(* alternative proof of wrwfp
val fplem' = prove_goal Drc.thy 
  "(Y ---> wlpm A Y && Q) --> (Y ---> wlpm (rep n A) Q)"
  (fn _ => [rtac impI 1, (induct_tac "n" 1), 
    etac liftimp_trans 1, Simp_tac 1,
    (simp_tac (HOL_ss addsimps [rep.rep_Suc, seq_wlp]) 1),
    (dtac (liftandD1 RSN (2, liftimp_trans)) 1),
    (eatac (wlpm_mono_cond RSN (2, liftimp_trans)) 1 1)]) RS mp ;

val _ = qed_goal_spec_mp "wrwfp'" Drc.thy 
  "(Y ---> wlpm A Y && Q) --> (Y ---> wlpm (repstar A) Q)"
  (fn _ => [strip_tac 1,
    (simp_tac (esimps [wlpca, repall_def', choice_wlp]) 1),
    Safe_tac, (dtac fplem' 1), Auto_tac]) ;
*)

(* proof of Hoare logic rule for while *)
val _ = qed_goal_spec_mp "wlpm_while" Drc.thy
  "(Y && b ---> wlpm c Y) --> (Y ---> wlpm (while b c) (Y && (Not o b)))"
  (fn _ => [ (rtac impI 1),
    (simp_tac (HOL_ss addsimps [while_def, seq_wlp]) 1),
    (rtac wrwfp' 1), (clarsimp_tac (cesimps [guard_wlp]) 1) ]) ;

(** relation between saf and cic **)

val _ = qed_goal_spec_mp "rep_trm_fis" Drc.thy 
  "~ trmm (rep m A) state --> fis (rep n A) state"
  let val ac' = read_instantiate_sg (sign_of Dmc.thy)
	  [("f", "rep")] arg_cong ;
    val th = le_add_diff_inverse RS ac' RS sym ;
    val [tfs, tsf] = map (meta_std o rewrite_rule [liftimp, o_def])
      [trm_fis_seq, trm_seq_fis] ;
    val thc = tacthm (etac rev_iffD2 2) contrapos_nn ;
    val (tfse, tsfe) = (tfs RS rev_iffD2, thc RS tsf) ;
  in (fn _ => [(case_tac "m < n" 1), (fold_tac [le_def]),
    Safe_tac, (dtac less_imp_le 1),
    (etac tfse 1), (etac tsfe 2), 
    (TRYALL (EVERY' [ (dtac th),
    ((gen_cong_tac) THEN' (gen_cong_tac) THEN_ALL_NEW (TRY o rtac refl)),
    (rtac trans), (rtac rep_plus o incr), 
    (gen_cong_tac THEN_ALL_NEW (ares_tac [refl])) ]))]) end ;

  (* formerly used following from level 3 on, but now
    asm_simp_tac step doesn't work 
  (TRYALL (EVERY' [TRY o dtac less_imp_le,
    dtac th, (asm_simp_tac (esimps [rep_plus])), 
    (rtac impI), (eresolve_tac [tfs, tsf])])) *)

val _ = qed_goalw_spec_mp "cic_saf" Drc.thy [cic_def, saf_def]
  "~ cic A state --> saf A state" 
  (fn _ => [Safe_tac, etac swap 1, etac rep_trm_fis 1]) ;

(** fixpoint formulation of trmm (repstar A),
  as in Steve's email of 28 Aug 2001;
  note - this is greatest (strongest) fixpoint of conditions;
  trm (A* ) = gfp of Y = wp (A, Y) **)

(* trmm (repstar A) and so is trmm (repall A) is a fixpoint *)

val [thra, thrs] = map (read_instantiate [("f", "trmm")])
  ([repall_seq, repstar_seq] RL [arg_cong]) ;

val trfp_tacs = [ (rtac ext 1),
  (simp_tac (esimps [seq_trm' RS sym]) 1),
  (simp_tac (esimps [thra, thrs, choice_trm]) 1)] ;

val _ = qed_goal "trfp" Drc.thy 
  "trmm (repstar A) = wpm A (trmm (repstar A))" (fn _ => trfp_tacs) ;

val _ = qed_goal "trallfp" Drc.thy 
  "trmm (repall A) = wpm A (trmm (repall A))" (fn _ => trfp_tacs) ;

val th1 = rewrite_rule [Let_def] trfp RS fun_cong ;
val th2 = rewrite_rule [wpm_def, liftand, wlpm_def] th1 ;

(* trmm (repstar A) is strongest fixpoint *)
val _ = qed_goal_spec_mp "trsfp'" Drc.thy 
  "(wpm A Y ---> Y) --> trmm (repstar A) ---> Y"
  (fn _ => [ Safe_tac, (simp_tac (esimps [trmm_def, repstar_nt]) 1),
    Safe_tac, (etac swap 1),
    (res_inst_tac [("X", "Collect (Not o Y)")] icnt.coinduct 1), 
    Simp_tac 1, (full_simp_tac (esimps defs_mng) 1), Fast_tac 1 ]) ; 

val trsfp = sym RS liftimp_refl' RS trsfp' ;

(* trmm (repall A) is weakest fixpoint *)
val trwfp' = prove_goal Drc.thy 
  "(Y ---> wpm A Y) --> (Y ---> trmm (rep n A))"
  (fn _ => [ (rtac impI 1), (induct_tac "n" 1), Simp_tac 1, 
    (simp_tac (HOL_ss addsimps [rep.rep_Suc, seq_trm']) 1), 
    (etac liftimp_trans 1), (etac wpm_mono_cond 1) ]) RS mp ;

val _ = qed_goal_spec_mp "trallwfp'" Drc.thy 
  "(Y ---> wpm A Y) --> (Y ---> trmm (repall A))"
  (fn _ => [ (rtac impI 1), 
    (simp_tac (esimps [repall_def', choice_trm]) 1),
    Safe_tac, (dtac trwfp' 1), Force_tac 1]) ;

val trallwfp = liftimp_refl' RS trallwfp' ;

(** section 11 - refinement **)

val _ = qed_goal_spec_mp "repall_ref_mono" Drc.thy 
  "gencref A B --> gencref (repall A) (repall B)"
  (fn _ => [ strip_tac 1, 
    (simp_tac (esimps [repall_def, gencref_alt]) 1), Safe_tac,
    dtac rep_ref_mono 1,
    (asm_full_simp_tac (esimps [gencref_alt]) 1), Fast_tac 1]) ;
    
val _ = qed_goal_spec_mp "repall_tref_mono" Drc.thy 
  "totcref A B --> totcref (repall A) (repall B)"
  (fn _ => [ strip_tac 1, 
    (simp_tac (esimps [repall_def, totcref_alt]) 1), Safe_tac,
    dtac rep_tref_mono 1,
    (asm_full_simp_tac (esimps [totcref_alt]) 1), Fast_tac 1]) ;
    
(* not true for totcref *)
val _ = qed_goal_spec_mp "infch_ref_mono" Drc.thy 
  "gencref A B --> infch B state --> infch A state"
  (fn _ => [ (simp_tac (esimps [infch_def, gencref_alt]) 1), Auto_tac]) ;

val _ = qed_goal_spec_mp "infch_ref_mono'" Drc.thy 
  "gencref A B --> infchs B <= infchs A"
  (fn _ => [ Safe_tac, (etac infchs.coinduct 1),
    (etac infchs.elims 1), (force_tac (cesimps [gencref_alt]) 1)]) ;

val _ = qed_goal_spec_mp "icnt_tref_mono" Drc.thy 
  "totcref A B --> icnt B <= icnt A"
  (fn _ => [ Safe_tac, (etac icnt.coinduct 1),
    (etac icnt.elims 1), (auto_tac (cesimps [totcref_alt]))]) ;

val _ = qed_goal_spec_mp "repstar_ref_mono" Drc.thy 
  "gencref A B --> gencref (repstar A) (repstar B)"
  (fn _ => [ strip_tac 1,
    (ftac (simplify (esimps [gencref_alt]) repall_ref_mono) 1), 
    (simp_tac (esimps [repstar_def, gencref_alt]) 1), Safe_tac,
    (TRYALL (etac allE THEN' datac subsetD 1)), Safe_tac,
    (datac infch_ref_mono 1 1), Safe_tac]) ;

val _ = qed_goal_spec_mp "repstar_tref_mono" Drc.thy 
  "totcref A B --> totcref (repstar A) (repstar B)"
  (fn _ => [ strip_tac 1, (ftac repall_tref_mono 1),
    (dtac icnt_tref_mono 1), (rewtac totcref_alt),
    (etac all_forward 1), (etac disj_forward 1),
    (asm_simp_tac (esimps [repstar_def]) 2),
    (Clarify_tac 1), (case_tac "x" 1),
    (force_tac (cesimps [repstar_nt]) 1),
    (force_tac (claset (),
      esimps [repstar_def] addsplits [split_if_asm]) 1) ]) ;

(** intuitive while **)

val _ = qed_goalw "while_prog" Drc.thy [while_def, ifthen_def] 
  "while Gm A = ifthen Gm (seq A (while Gm A))"
  (fn _ => [
    let val th = repstar_seq RS arg_cong RS trans ;
    in (res_inst_tac [("f1", "%x. seq x ?y")] th 1) end,
    (rewrite_tac (map mk_eq [Xguard RS sym, seq_assoc, seq_choiceL])),
    (Simp_tac 1)]) ;

