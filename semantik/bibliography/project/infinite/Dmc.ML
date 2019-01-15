
structure Dmc = struct val thy = theory "Dmc" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
val _ = use_legacy_bindings Dmc.thy ;

val infchs_mk_cases = Dmc.ipt_mk_cases "Dmc.infchs" ;

fun uta() = update_thy "Dall" ;
fun utoa() = update_thy_only "Dall" ;
fun ua() = use "Dall.ML" ;

fun utmc() = update_thy "Dmc" ;
fun utomc() = update_thy_only "Dmc" ;
fun umc() = use "Dmc.ML" ;

val conc_def' = rewrite_rule [concrs_def] conc_def ;
val pcomp_def' = rewrite_rule [pcomprs_def] pcomp_def ;

val defs_mc = defs_mng @ [ precon_def, guard_def, concrs_def, pcomprs_def,
  conc_def, pcomp_def, choice_def, 
  fis_def, abt_def, cic_def, saf_def,
  atd_def, prdm_def, prdtm_def ] ;

val cs_mc = cesimps defs_mc ;

fun ft_mc _ = [REPEAT (resolve_tac [set_ext, ext, impI] 1), auto_tac cs_mc] ;

(** useful lemmas *)

val _ = qed_goal "guard_True" Dmc.thy "guard (%st. True) A = A" ft_mc ;

val _ = qed_goal "guard_alt" Dmc.thy 
  "x : guard P C s = (P s & x : C s)" ft_mc ;

val _ = qed_goalw "choice_guard" Dmc.thy defs_mng
  "choice ((guard P) ` Cs) = guard P (choice Cs)" ft_mc ;

val _ = qed_goal "choice_trm" Dmc.thy
  "trmm (choice Cs) state = (ALL C : Cs. trmm C state)" ft_mc ;

val _ = qed_goal "choice_wp" Dmc.thy
  "wpm (choice Cs) Q state = (ALL C : Cs. wpm C Q state)" ft_mc ;

val _ = qed_goal "choice_wlp" Dmc.thy
  "wlpm (choice Cs) Q state = (ALL C : Cs. wlpm C Q state)" ft_mc ;

val _ = qed_goal "rep_unit" Dmc.thy 
  "rep n unitos = unitos" 
  (fn _ => [(induct_tac "n" 1), Simp_tac 1,
    (asm_simp_tac (HOL_ss addsimps [rep.rep_Suc, seq_unitL]) 1) ]) ;

val _ = qed_goal "choice_single" Dmc.thy "choice {C} = C" ft_mc ;
val _ = qed_goal "choice_empty" Dmc.thy "choice {} = magic" ft_mc ;

val _ = qed_goal_spec_mp "choice_mono" Dmc.thy 
  "Cs' <= Cs --> choice Cs' state <= choice Cs state" ft_mc ;

Addsimps [ guard_True, rep_unit, choice_single] ;

val [th1, th2] = [choice_def RS def_imp_eq RS set_cong] RL [iffD1, iffD2] ;

val _ = ListPair.app bind_thm (["choiceI", "choiceE"], 
  [(UN_I RS th2), (th1 RS UN_E)]) ;

(* Dunne's frame limitation result - condition is
  if Q does not involve variables in frame (A) -- becomes
  executing A cannot change Q *)

val _ = qed_goal "frame_limit" Dmc.thy
  "(ALL state nst. Term nst : A state --> Q nst = Q state) --> \
    \ wlpm A Q = (wlpm A (%st. False) V Q)" ft_mc ;

(** section 4 - preconditioned command **)

val _ = qed_goal "precon_wp" Dmc.thy 
  "wpm (precon P C) Q = (P && wpm C Q)" ft_mc ;

val _ = qed_goal "precon_wlp" Dmc.thy 
  "wlpm (precon P C) = wlpm C" ft_mc ;

val _ = qed_goal "precon_trm" Dmc.thy 
  "trmm (precon P C) = (P && trmm C)" ft_mc ;

val _ = qed_goal "pc_trm" Dmc.thy "(precon (trmm A) A) = A" ft_mc ;

val _ = qed_goal "term_precon" Dmc.thy 
  "terms (precon C A) = terms A" ft_mc ;

val _ = qed_goal "precon_Term" Dmc.thy 
  "(Term fun : precon C A state) = (Term fun : A state)" ft_mc ;

Addsimps [precon_Term, term_precon] ;

(* intuition about precon - allows non-termination when condition fails *)

val _ = qed_goal "pc_nonterm" Dmc.thy 
  "(precon C A) = (choice { A, guard (Not o C) abort})" ft_mc ;

val _ = qed_goal_spec_mp "precon_choice" Dmc.thy 
  "As ~= {} --> (precon C (choice As)) = (choice (precon C ` As))" ft_mc ;

val _ = bind_thm ("precon_choice_range", 
  rangeI RS tacthm (etac equals0D 2) contrapos_pn RS precon_choice) ;

val _ = qed_goalw "choice_abort" Dmc.thy [totceqv_alt, choice_def]
  "totceqv (choice (insert abort cs)) abort"
  (fn _ => [ (force_tac (cis [insertI1 RS UN_I], esimps [abort_def]) 1) ]) ;

(** section 4 - guarded command **)

val _ = qed_goal "guard_wp" Dmc.thy 
  "wpm (guard P C) Q state = (P state --> wpm C Q state)" ft_mc ;

val _ = qed_goal "guard_wlp" Dmc.thy 
  "wlpm (guard P C) Q state = (P state --> wlpm C Q state)" ft_mc ;

val _ = qed_goal "guard_trm" Dmc.thy 
  "trmm (guard P C) state = (P state --> trmm C state)" ft_mc ;

(* assertively preconditioned form, section 5.1 *)
val _ = qed_goal "ass_precon" Dmc.thy 
  "precon P (guard P A) state = (if P state then A state else {NonTerm})"
  ft_mc ;

val _ = qed_goal_spec_mp "seq_choiceR" Dmc.thy 
  "(cs ~= {}) --> (seq A (choice cs) = choice (seq A ` cs))"
  (fn _ => [ (rtac impI 1), (rtac ext 1), 
    (safe_tac (claset () addSEs [choiceE, seqE])),
    (TRYALL (rtac (imageI RS choiceI))),
    (TRYALL (eresolve_tac [seqIT, seqINT])),
    (TRYALL atac), (eatac choiceI 1 1)]) ;

val _ = qed_goal "seq_choiceL" Dmc.thy 
  "seq (choice cs) B = choice ((%C. seq C B) ` cs)"
  (fn _ => [ (rtac ext 1), 
    (safe_tac (claset () addSEs [choiceE, seqE])),
    (TRYALL (rtac (imageI RS choiceI))),
    (TRYALL (resolve_tac [seqINT, seqIT])),
    (TRYALL atac), (TRYALL (eatac choiceI 1))]) ; 

val _ = qed_goal "Xpre" Dmc.thy 
  "seq (precon P A) B = precon P (seq A B)" ft_mc ;
  
val _ = qed_goal "Xguard" Dmc.thy 
  "seq (guard P A) B = guard P (seq A B)" ft_mc ;

val _ = qed_goal "gia_seq" Dmc.thy
  "seq (guard (infch C) abort) C = (guard (infch C) abort)"
  (fn _ => [ (simp_tac (esimps [Xguard, seq_abort]) 1) ]) ;

(** section 5.2 **)

val _ = qed_goal "Xassump" Dmc.thy 
  "guard P A = seq (guard P unitos) A" 
  (fn _ => [ (simp_tac (esimps [Xguard]) 1)]) ;
  
val _ = qed_goal "Xassert" Dmc.thy 
  "precon P (guard P A) = seq (precon P (guard P unitos)) A"
  (fn _ => [ (simp_tac (esimps [Xpre, Xassump RS sym]) 1)]) ;

(** section 5.1 **)
val _ = qed_goal "perhaps_alt" Dmc.thy 
  "perhaps = precon (%st. False) unitos" ft_mc ;

val _ = qed_goal "magic_alt" Dmc.thy
  "magic = guard (%st. False) A" ft_mc ;

val _ = qed_goal "abort_alt" Dmc.thy
  "abort = precon (%st. False) (guard (%st. False) A)" ft_mc ;

val _ = qed_goal "asp" Dmc.thy "choice {abort, unitos} = perhaps" ft_mc ;

(** section 7 **)

val _ = qed_goalw "fis_def'" Dmc.thy 
  [meta_eq_def, fis_def, wpm_def, liftand, wlpm_def, trmm_def]
  "fis A state == Not (wpm A (%x. False) state)" 
  (fn _ => [Safe_tac, (case_tac "x" 1), Auto_tac]) ;

val _ = qed_goalw "fis_or_wp" Dmc.thy [fis_def'] "fis S s | wpm S Q s"
  (fn _ => [ Safe_tac, (etac notE 1), 
    (etac wpm_mono_cond_alt' 1), Simp_tac 1 ]) ;

val _ = qed_goal "fis_guard" Dmc.thy 
  "(guard (fis A) A) = A" ft_mc ;

val _ = qed_goal "abt_def'" Dmc.thy 
  "abt A = ((Not o trmm A) && wlpm A (%x. False))" 
  (fn _ => [rtac ext 1, 
    rewrite_goals_tac [abt_def, o_def, wpm_def, liftand, wlpm_def, trmm_def],
    Safe_tac, (case_tac "xa" 3), Auto_tac]) ;

(** section 9 - if then else - definition given matches intuition **)

val _ = qed_goal "if_gc" Dmc.thy
  "(if P state then A state else B state) = \
    \ choice {guard P A, guard (Not o P) B} state" ft_mc ;

(** section 10 - pcomp and conc, parallel composition **) 

val _ = qed_goal "conc_trm" Dmc.thy
  "trmm (conc A B) = (trmm A V trmm B)" ft_mc ;

val _ = qed_goal "conc_wlp" Dmc.thy
  "wlpm (conc A B) Q = (wlpm A Q && wlpm B Q)" ft_mc ;

val _ = qed_goal "conc_magic" Dmc.thy
  "(conc A magic state) = (A state - {NonTerm})" ft_mc ;

val _ = qed_goal "pcomp_trm" Dmc.thy
  "trmm (pcomp A B) = (trmm A && trmm B)" ft_mc ;

val _ = qed_goal "conc_pcomp" Dmc.thy
  "pcomprs cr1 cr2 = - (concrs (- cr1) (- cr2))" ft_mc ;

val _ = qed_goal "conc_lemma" Dmc.thy
  "choice {guard P A, guard (Not o P) B} = \
    \ conc (precon P (guard P A)) \
    \ (precon (Not o P) (guard (Not o P) B))" ft_mc ;

val _ = qed_goal "pcomp_choice" Dmc.thy
  "pcomp B (choice (insert A As)) = choice (pcomp B ` (insert A As))" ft_mc ;

(*
val _ = [ precon_trm, precon_wlp, guard_trm, guard_wlp, seq_trm, seq_wlp,
  choice_trm, choice_wlp, conc_trm, conc_wlp ] ;
*)

(* Steve's email of 10 Sep - note, choice of Q1, Q2 depends on state *)
val _ = qed_goalw "pcomp_wlp" Dmc.thy 
  [wlpm_def, pcomp_def, pcomprs_def, liftand, liftimp]
  "wlpm (pcomp A B) Q state = \
    \ (EX Q1 Q2. (Q1 && Q2 ---> Q) & \
    \ wlpm A Q1 state & wlpm B Q2 state)" 
  (fn _ => [Safe_tac, Fast_tac 2, 
    (res_inst_tac [("x", "%nst. Term nst : A state")] exI 1), 
    (res_inst_tac [("x", "%nst. Term nst : B state")] exI 1), 
    Fast_tac 1]) ;

(** relation between trm and fis **)

val _ = qed_goal "trm_seq_fis" Dmc.thy 
  "Not o (trmm (seq A B)) ---> fis (A)" ft_mc ;

val _ = qed_goal "trm_fis" Dmc.thy "(trmm A s) | fis (A) s" ft_mc ;

val _ = qed_goalw "trm_fis_seq" Dmc.thy [o_def, liftimp, trmm_def, fis_def]
  "Not o (trmm (A)) ---> fis (seq A B)" 
  (fn _ => [Safe_tac, 
    (dtac equals0D 1), (etac notE 1), (etac seq.INT 1) ]) ;

(** section 11 - refinement, monotonicity **)

val _ = qed_goalw_spec_mp "choice_gencref" Dmc.thy [choice_def, gencref_alt]
  "C : Cs --> gencref (choice Cs) C" fn_at ;

val choice_totcref = rewrite_rule [gencref_def'] choice_gencref RS
  conjunct2 ;

val _ = qed_goalw "choice_glb" Dmc.thy [choice_def, gencref_alt]
  "gencref A (choice Cs) = (ALL C:Cs. gencref A C)" fn_at ;

val _ = qed_goal "top_magic" Dmc.thy "gencref A magic"
  (fn _ => [ (simp_tac (esimps [choice_empty RS sym, choice_glb]) 1) ]) ;

val _ = qed_goalw_spec_mp "concert_ref_mono" Dmc.thy [gencref_alt, conc_def']
  "gencref A1 B1 --> gencref A2 B2 --> gencref (conc A1 A2) (conc B1 B2)"
  fn_ft1 ;

val _ = qed_goalw_spec_mp "pcomp_ref_mono" Dmc.thy [gencref_alt, pcomp_def']
  "gencref A1 B1 --> gencref A2 B2 --> gencref (pcomp A1 A2) (pcomp B1 B2)"
  fn_ft1 ;

val _ = qed_goalw_spec_mp "pcomp_tref_mono" Dmc.thy [totcref_alt, pcomp_def']
  "totcref A1 B1 --> totcref A2 B2 --> totcref (pcomp A1 A2) (pcomp B1 B2)"
  fn_ft1 ;

val _ = qed_goalw_spec_mp "choice2_ref_mono" Dmc.thy [gencref_alt, choice_def]
  "gencref A1 B1 --> gencref A2 B2 --> \ 
    \ gencref (choice {A1, A2}) (choice {B1, B2})" fn_ft1 ;

val _ = qed_goalw_spec_mp "gencref_choice" Dmc.thy [gencref_alt, choice_def]
  "(ALL s:S. gencref (f s) (g s)) --> \
    \ gencref (choice (f ` S)) (choice (g ` S))" fn_at ;

val _ = qed_goalw_spec_mp "totcref_choice" Dmc.thy [totcref_def]
  "(ALL s:S. totcref (f s) (g s)) --> \
    \ totcref (choice (f ` S)) (choice (g ` S))" 
  (fn _ => [ (auto_tac (cesimps [choice_wp])) ]) ;

val _ = qed_goalw_spec_mp "totceqv_choice" Dmc.thy [totceqv_def]
  "(ALL s:S. totceqv (f s) (g s)) --> \
    \ totceqv (choice (f ` S)) (choice (g ` S))" 
  (fn _ => [ (fast_tac (cis [totcref_choice]) 1) ]) ;

val _ = qed_goalw_spec_mp "precon_ref_mono" Dmc.thy [gencref_alt]
  "gencref A B --> gencref (precon P A) (precon P B)" ft_mc ;
val _ = qed_goalw_spec_mp "guard_ref_mono" Dmc.thy [gencref_alt]
  "gencref A B --> gencref (guard P A) (guard P B)" ft_mc ;

val _ = qed_goalw_spec_mp "precon_tref_mono" Dmc.thy [totcref_alt]
  "totcref A B --> totcref (precon P A) (precon P B)" ft_mc ;
val _ = qed_goalw_spec_mp "guard_tref_mono" Dmc.thy [totcref_alt]
  "totcref A B --> totcref (guard P A) (guard P B)" ft_mc ;

val _ = qed_goal_spec_mp "rep_tref_mono" Dmc.thy 
  "totcref A B --> totcref (rep n A) (rep n B)"
  (fn _ => [ strip_tac 1, (induct_tac "n" 1), 
    (simp_tac (esimps [totcref_alt, unitos_def]) 1),
    (Simp_tac 1), (eatac seq_tref_mono 1 1)]) ;

val _ = qed_goal_spec_mp "rep_ref_mono" Dmc.thy 
  "gencref A B --> gencref (rep n A) (rep n B)"
  (fn _ => [ strip_tac 1, (induct_tac "n" 1), 
    (simp_tac (esimps [gencref_alt, unitos_def]) 1),
    (Simp_tac 1), (eatac seq_ref_mono 1 1)]) ;

val _ = qed_goal "conc_not_tot_ref_mono" Dmc.thy 
  "~ (totcref abort unitos --> totcref (conc abort magic) (conc unitos magic))"
  (fn _ => [ (simp_tac (esimps (totcref_alt :: defs_mc)) 1)]) ;

(** the Galois connection, Lermer, Fidge, Hayes, CATS 2003, Thm 6.1 **)

(* Thm 6.1 (iii), (iv) *)
val th61iii = prove_goal Dmc.thy 
  "wlpm S = wlpm (seq (guard (Not o wlpm S (%st. False)) unitos) S)" 
  (fn _ => [ (simp_tac (esimps [Xassump RS sym]) 1), 
    (REPEAT (rtac ext 1)), (simp_tac (esimps [wlpm_def, guard_def]) 1)]) ; 

val th61iv = prove_goal Dmc.thy 
  "wlpm S = wlpm (seq S (guard (slpm S (%st. True)) unitos))" 
  (fn _ => [ (REPEAT (rtac ext 1)), (force_tac (cesimps 
      [seq_wlp, wlpm_def, guard_def, slpm_def, unitos_def]) 1)]) ; 

(** prdm and prdtm **)
val _ = qed_goal "pcomp_prd" Dmc.thy
  "prdm primed (pcomp A B) = (prdm primed A && prdm primed B)" ft_mc ;
    
(* Dunne, A Theory of Generalised Substitutions. ZB2002 s 6 *)
val _ = qed_goal "pcomp_prdt" Dmc.thy "prdtm primed (pcomp A B) s = \
    \ ((trmm B s --> prdtm primed A s) & (trmm A s --> prdtm primed B s))" 
  ft_mc ;
    
val _ = qed_goal "pcomp_prdt_alt" Dmc.thy "prdtm primed (pcomp A B) s = \
    \ (trmm (pcomp A B) s --> prdtm primed A s & prdtm primed B s)" 
  ft_mc ;
    
val _ = qed_goal "prdt_prd" Dmc.thy 
  "prdtm primed S s = (trmm S s --> prdm primed S s)" ft_mc ;

(* prop 7 of Dunne, A Theory of Generalised Substitutions. ZB2002 *) 
val _ = qed_goalw "totcref_prdt" Dmc.thy 
  [liftimp, o_def, totcref_def, prdtm_def]
  "totcref A B = ((trmm A ---> trmm B) & \
    \ (ALL primed. prdtm primed B ---> prdtm primed A))"
  (fn _ => [Safe_tac,
    (force_tac (cesimps [wp_trm]) 1), Fast_tac 1, 
    (full_simp_tac (esimps defs_mng) 1), Fast_tac 1]) ;

val _ = qed_goalw "partcref_prd" Dmc.thy 
  [liftimp, o_def, partcref_def, prdm_def]
  "partcref A B = (ALL primed. prdm primed B ---> prdm primed A)"
  (fn _ => [Safe_tac, Fast_tac 1, rewtac wlpm_def, Safe_tac,
    (eres_inst_tac [("x", "nst")] allE 1), Fast_tac 1]) ;

val _ = qed_goalw "trm_or_prdtm" Dmc.thy [prdtm_def] 
  "trmm S s | prdtm primed S s"
  (fn _ => [ (auto_tac (cis [wp_imp_trm'], esimps [])) ]) ;

val _ = qed_goalw "prdtm_imp_fis" Dmc.thy [liftimp, prdtm_def] 
  "prdtm primed S ---> fis S"
  (fn _ => [ Auto_tac, (rtac (fis_or_wp RS disjE) 1), Auto_tac ]) ;

(* last result of section 7.0 *)
val _ = qed_goalw "wlp_prd" Dmc.thy [o_def, prdm_def, wlpm_def]
  "wlpm A Q state = (ALL primed. prdm primed A state --> Q primed)" fn_at ;

val _ = qed_goalw "wp_prd" Dmc.thy 
  [o_def, prdtm_def, wpm_def, wlpm_def, liftand]
  "wpm A Q state = (trmm A state & \
    \ (ALL primed. prdtm primed A state --> Q primed))" fn_at ;

val _ = qed_goal "atd_choice" Dmc.thy "atd Ad = choice (range Ad)" ft_mc ;

val _ = qed_goal "ACNF" Dmc.thy 
  "A = precon (trmm A) \
    \ (atd (%primed. guard (prdm primed A) (%st. {Term primed})))"
  (fn _ => [(ft_ss (split_if_asm :: defs_mc)),
    (ALLGOALS (case_tac "xa")), Auto_tac]) ;
    
(* versions for total correctness *)
val _ = qed_goalw "ACNF_tc'" Dmc.thy [totceqv_alt]
  "totceqv A (precon (trmm A) \
    \ (atd (%primed. guard (prdtm primed A) (%st. {Term primed}))))"
  (fn _ => [(ft_ss (split_if_asm :: defs_mc)),
    (ALLGOALS (case_tac "x")), Auto_tac]) ;
    
val _ = qed_goalw_spec_mp "pca_lem" Dmc.thy (totceqv_alt :: defs_mc)
  "(ALL s. (Cp s) --> Cg1 s = Cg2 s) --> \
    \ totceqv (precon Cp (guard Cg1 A)) (precon Cp (guard Cg2 A))"
  (fn _ => [ (strip_tac 1), 
    (eres_inst_tac [("x", "s")] allE 1), Auto_tac ]) ; 
    
(* expression for S || T, s6 of Dunne, ZB2002, LNCS 2272, pg 277 *)
val _ = qed_goal "pcomp_alt" Dmc.thy
  "totceqv (pcomp S T) (precon (trmm S && trmm T) (atd (%primed. \
      \ guard (prdtm primed S && prdtm primed T) (%st. {Term primed}))))"
  (fn _ => [ (rtac totceqv_trans 1), (rtac ACNF_tc' 1),
    (simp_tac (esimps [atd_choice, precon_choice_range]) 1),
    (simp_tac (esimps [image_compose RS sym, pcomp_trm]) 1),
    (rtac totceqv_choice 1), Clarsimp_tac 1,
    (rtac pca_lem 1), (clarsimp_tac (cesimps [pcomp_prdt]) 1) ]) ; 

(* ACNF-like expression for lub of two commands, s7 of Dunne, 
  A Theory of Generalised Substitutions. ZB2002, LNCS 2272, 270-290. *)

val _ = qed_goal "lub" Dmc.thy 
  "precon (trmm A V trmm B) \
    \ (atd (%primed. guard (prdm primed A && prdm primed B) \
    \ (%st. {Term primed}))) state = (A state Int B state)"
  (fn _ => [ (simp_tac (esimps defs_mc) 1), Safe_tac,
    (ALLGOALS (full_simp_tac (simpset () addsimps [split_if_asm]))),
    (TRYALL Fast_tac), (ALLGOALS (case_tac "x")), (TRYALL Fast_tac)]) ; 
    

(** wreach, wrrel, rep etc **)
val _ = bind_thm ("wreach1", [asm_rl, refl, wreach.wr_0] MRS wreach.wr_Suc) ;

AddIffs [wreach.wr_0, wrrel.wr_0] ;
AddSEs [wrrel.wr1, wreach1] ;
val infchsE = infchs_mk_cases "x : infchs C" ;

val [infchs_coinduct, icnt_coinduct] =
  map (rewrite_rule [mk_eq mem_Collect_eq] o
    read_instantiate [("X", "Collect ?P")]) 
  [infchs.coinduct, icnt.coinduct] ;

val wr_Suc' = refl RSN (2, wreach.wr_Suc) ;

val _ = qed_goal "wreach_rel" Dmc.thy 
  "((s, cr) : wrrel C) = (cr : wreach C s)"
  (fn _ => [ Safe_tac,
    (etac wrrel.induct 1), Fast_tac 1, 
    (etac thin_rl 1), (etac wreach.induct 1), 
    (REPEAT (ares_tac (refl :: wreach.intros) 1)),
    (etac wreach.induct 1), Fast_tac 1, 
    (etac rev_mp 1), (etac rev_mp 1),
    (etac wrrel.induct 1), Safe_tac,
    (ALLGOALS (rtac wrrel.wr_Suc)), Auto_tac]) ;

val _ = qed_goal "wr_seq" Dmc.thy 
  "seq (wreach C) C state <= wreach C state"
  (fn _ => [(rtac subsetI 1), (etac seqE 1), Fast_tac 1,
    (eatac wr_Suc' 1 1)]) ;

val _ = qed_goal "wr_ch" Dmc.thy 
  "wreach C = choice {seq (wreach C) C, unitos}" 
  (fn _ => [ (rtac ext 1), (rewtac choice_def), Safe_tac,
    (etac (wr_seq RS subsetD) 2), (etac wreach.elims 1), 
    (auto_tac (cis [seqIT], esimps [unitos_def]))]) ;

val _ = qed_goal "wr_ch'" Dmc.thy 
  "wreach C state = insert (Term state) (seq (wreach C) C state)" 
  (fn _ => [Safe_tac, (etac (wr_seq RS subsetD) 2),
    (etac wreach.elims 1), (auto_tac (cis [seqIT], simpset ()))]) ;

val _ = qed_goal "seq_wrr" Dmc.thy 
  "seq C (wreach C) state <= wreach C state"
  (fn _ => [(rtac subsetI 1), (etac seqE 1), (rtac wr_Suc' 1),
    (auto_tac (cesimps [wreach_rel RS sym])),
    (eatac wrrel.wr_Suc 1 1) ]) ;

val _ = qed_goal "wr_chr'" Dmc.thy 
  "wreach C state = insert (Term state) (seq C (wreach C) state)" 
  (fn _ => [Safe_tac, (etac (seq_wrr RS subsetD) 2),
    (full_simp_tac (esimps [wreach_rel RS sym]) 1),
    (etac wrrel.elims 1), Fast_tac 1, (ALLGOALS (etac notE)),
    (case_tac "cr" 2), (clarify_tac (ces [seqINT]) 2),
    (auto_tac (cis [seqIT], esimps [wreach_rel RS sym]))]) ;

val _ = qed_goal "wr_chr" Dmc.thy 
  "wreach C = choice {seq C (wreach C), unitos}" 
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [choice_def, wr_chr', unitos_def]) 1) ]) ;
  
val _ = qed_goal "wrE" Dmc.thy
  "[| cr : wreach C state; cr = Term state ==> R; \
    \ cr : seq (wreach C) C state ==> R |] ==> R"
  (fn [p1, p2, p3] => [(cut_facts_tac [p1] 1), 
    (etac wreach.elims 1), etac p2 1, 
    (rtac (seqIT RS p3) 1), (Auto_tac)]) ;

val _ = qed_goal "seq_wr" Dmc.thy 
  "seq (wreach C) C = seq C (wreach C)"
  (fn _ => [ (rtac trans 1), 
    (freeze_tac (stac wr_chr 1 THEN stac wr_ch 2)), (rtac refl 2), 
    (simp_tac (esimps [seq_choiceL, seq_choiceR, seq_assoc]) 1)]) ;

val _ = qed_goal "wreach_unitos" Dmc.thy "wreach unitos = unitos"
  (fn _ => [ (rtac ext 1), Safe_tac, (etac wreach.induct 1),
    (rewtac unitos_def), Auto_tac ]) ;

val _ = qed_goal "rep_Suc'" Dmc.thy
  "rep (Suc n) C = seq (rep n C) C"
  (fn _ => [(induct_tac "n" 1), (Simp_tac 1),
    (rtac (trans RS trans) 1), 
    (rtac rep.rep_Suc 1), (Simp_tac 2),
    (asm_simp_tac HOL_ss 1), rtac seq_assoc 1]) ;

val cic_next = meta_std (prove_goalw Dmc.thy [cic_def, fis_def]
  "Term nst : C state & cic C nst --> cic C state"
  (fn _ => [Safe_tac, 
    (case_tac "n" 1), (asm_full_simp_tac (esimps [unitos_def]) 1),
    (eres_inst_tac [("x", "nat")] allE 1),
    Asm_full_simp_tac 1, (safe_tac (cis [equals0I])),
    (dres_inst_tac [("state", "state")] seq.IT 1), Auto_tac])) ;

val _ = qed_goalw_spec_mp "cic_NT" Dmc.thy [cic_def, fis_def]
  "NonTerm : C state --> cic C state"
  (fn _ => [Safe_tac, 
    (case_tac "n" 1), (asm_full_simp_tac (esimps [unitos_def]) 1),
    Asm_full_simp_tac 1,
    (dtac equals0D 1), (etac notE 1), (etac seq.INT 1) ]) ;

(* the following result, if true, would say that whenever cic C state holds,
  then it is in the situation either of cic_next or of cic_NT;

  "[| cic C state ; !! nst. [| Term nst : C state ; cic C nst |] ==> P ; \
    \ NonTerm : C state ==> P |] ==> P"

  In fact that is not so.  Imagine that C produces an infinite number of
  next states (call them nst_0, nst_1, ...).
  Imagine that, starting from nst_k, C can be feasibly repeated k times 
  but no more.  Then cic C state holds, but cic C nst_k does not hold
  for any k.
  
  A definition fitting the description "infinite chains" is infch_def *)

(* equivalence of infch and infchs *)

val _ = qed_goalw_spec_mp "infchs_isuc" Dmc.thy [isuc_def] 
  "s : infchs A --> ns = isuc A s --> Term ns : A s & ns : infchs A"
  (fn _ => [ (Clarify_tac 1), (etac infchs.elims 1),
    (rtac someI 1), (Fast_tac 1) ]) ;

val infchs_isuc' = refl RSN (2, infchs_isuc) ;

val _ = qed_goalw "infch_s" Dmc.thy [meta_eq_def, infch_def]
  "infch A s == (s : infchs A)"
  (fn _ => [ Safe_tac, 
    ((res_inst_tac [("X", "range f")] infchs.coinduct 
      THEN_ALL_NEW Fast_tac) 1), 
    (res_inst_tac [("x", "infch_of A s")] exI 1), 
    (subgoal_tac "ALL m. infch_of A s m : infchs A" 1),
    (rtac allI 2), (induct_tac "m" 2),
    (ALLGOALS (clarsimp_tac (cesimps [infch_of_def]))),
    (etac (infchs_isuc' RS conjunct2) 2),
    (eres_inst_tac [("x", "n")] allE 1),
    (etac (infchs_isuc' RS conjunct1) 1) ]) ;

val _ = qed_goal "infchs_nt" Dmc.thy "infchs A <= icnt A"
  (fn _ => [ Safe_tac, (etac icnt.coinduct 1),
    (etac infchs.elims 1), Fast_tac 1]) ;

val _ = qed_goal_spec_mp "icnt_chs_wr" Dmc.thy 
  "(s : icnt A) = (s : infchs A | (s, NonTerm) : wrrel A)"
  (fn _ => [ (rtac iffI 1), (etac icnt_coinduct 2), 
    (etac disjE 2), (etac wrrel.elims 3), (etac infchsE 2), 
    (rtac disjCI 1), (datac conjI 1 1), (etac thin_rl 1),
    (etac infchs_coinduct 1), (etac conjE 1),
    (etac icnt.elims 1), (dtac wrrel.wr1 2),
    (dtac (tacthm (etac wrrel.wr_Suc 2) contrapos_nn) 1),
    (TRYALL Fast_tac) ]) ;
  
val _ = qed_goalw "infch_skip" Dmc.thy [infch_def] "infch unitos state" ft_mc ;

(*
val infch_next = meta_std (prove_goalw Dmc.thy [infch_def]
  "Term nst : C state & infch C nst --> infch C state"
  (fn _ => [Safe_tac, 
    (res_inst_tac [("x", 
      "%i. case i of 0 => state | Suc n => f n")] exI 1),
    Auto_tac, (case_tac "n" 1), Auto_tac])) ;
*)

val infch_next = fold_rule [infch_s] infchs.I ;
val ninfch_next = tacthm (etac (rotate_prems 1 infch_next) 2) contrapos_nn ;

val _ = qed_goalw_spec_mp "infch_prev_eq" Dmc.thy [infch_s]
  "infch C state = (EX nst. Term nst : C state & infch C nst)"
  (fn _ => [ Safe_tac, (etac infchs.elims 1),
    (rtac infchs.intros 2), Auto_tac ]) ;

val infch_prev = standard (infch_prev_eq RS iffD1) ;

(*
val _ = qed_goalw_spec_mp "infch_prev" Dmc.thy [infch_def]
  "infch C state --> (EX nst. Term nst : C state & infch C nst)"
  (fn _ => [Safe_tac, 
    (res_inst_tac [("x", "f 1")] exI 1), Safe_tac, 
    (res_inst_tac [("x", "f o Suc")] exI 2), Auto_tac]) ;
*)

val _ = map store_thm [
  ("seq_term", seq_term),
  ("cic_next", cic_next),
  ("infch_next", infch_next),
  ("ninfch_next", ninfch_next) ] ;

