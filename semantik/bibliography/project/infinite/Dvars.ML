
structure Dvars = struct val thy = theory "Dvars" end ;
val _ = use_legacy_bindings Dvars.thy ;

fun uts() = update_thy "Dvars" ;
fun utos() = update_thy_only "Dvars" ;
fun us() = use "Dvars.ML" ;

val defs_vars = [allvars_def, assigne_def, assignv_def, assignvs_def, 
  at_def, chst_def, indetass_def, prds_def,
  prdts_def, setvars_def, revert_def] @ defs_mc ;

val cs_vars = cesimps defs_vars ;
fun ft_vars _ = [REPEAT (resolve_tac [ext, impI] 1), auto_tac cs_vars] ;

val () = qed_goal "setvars_ow" Dvars.thy "setvars A g f = override_on f g A"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [setvars_def]) 1)]) ;

(* ordinary assignment *)
val _ = qed_goalw "ass_trm" Dvars.thy [trmm_def, assigne_def, assignv_def]
  "trmm (assigne x E) state = True" (fn _ => [Fast_tac 1]) ;

val _ = qed_goalw "ass_wlp" Dvars.thy [wlpm_def, assigne_def, assignv_def]
  "wlpm (assigne x E) Q st = Q (st (x := E st))" fn_ft1 ;

val _ = qed_goalw "ass_wp" Dvars.thy [wpm_def]
  "wpm (assigne x E) Q st = Q (st (x := E st))" 
  (fn _ => [ (simp_tac (esimps [ass_wlp, ass_trm]) 1) ]) ;

val petacs = [(REPEAT (rtac ext 1)),
  (rewrite_tac [prdm_def, prdtm_def, o_def, prds_def, prdts_def]),
  (cong_tac 1), rtac ext 1, rewtac (mk_eq fun_cong_all), Fast_tac 1] ;

val _ = qed_goal "prdm_def'" Dvars.thy "prdm = prds UNIV" (fn _ => petacs) ;
val _ = qed_goal "prdtm_def'" Dvars.thy "prdtm = prdts UNIV" (fn _ => petacs) ;

val rev_impE = reop (fn [a,b,c] => [a,c,b]) impE ;

(*
val _ = qed_goal "prdtm_frame" Dvars.thy [chst_def, frame_def,
  o_def, prdts_def, prdtm_def, liftand, wpm_def, wlpm_def]
  "frame A f --> (p, s) : chst f --> prdtm p A s = prdts f p A s" 
  (fn _ => [ Safe_tac,
    (REPEAT (etac allE 2)), (REPEAT (etac rev_impE 2)),
    (TRYALL atac)
   ]) ;
*)

val _ = qed_goal "precon_prd" Dvars.thy 
  "prds vars primed (precon P C) = prds vars primed C" ft_vars ;

val _ = qed_goal "setvars_UNIV" Dvars.thy "setvars UNIV sa sb = sa" ft_vars ;
val _ = qed_goal "setvars_empty" Dvars.thy "setvars {} sa sb = sb" ft_vars ;
    
val _ = qed_goal "setvars_comp" Dvars.thy 
  "setvars (- vars) sa sb = setvars vars sb sa" ft_vars ;
    
val _ = qed_goal "setvars_same" Dvars.thy "setvars vars st st = st"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [setvars_def]) 1) ]) ;

val _ = qed_goal "setvars_o" Dvars.thy
  "setvars vars g o setvars vars f = setvars vars g"
  (fn _ => [ (REPEAT (rtac ext 1)), (simp_tac (esimps [setvars_def]) 1) ]) ;

val _ = qed_goal "setvars_set" Dvars.thy
  "setvars vars (setvars vars sb fun) = setvars vars sb"
  (fn _ => [ (REPEAT (rtac ext 1)), (simp_tac (esimps [setvars_def]) 1) ]) ;

Addsimps [setvars_UNIV, setvars_empty, setvars_comp,
  setvars_same, setvars_set, mk_ap setvars_o] ;

val _ = qed_goal "upd_setvars" Dvars.thy 
  "st (v := t) = setvars {v} (%x. t) st"
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [setvars_def]) 1) ]) ;

val _ = qed_goalw "chst_setvarsI" Dvars.thy [chst_def] 
  "((st, setvars vars sf st) : chst vars)"
  (fn _ => [ (simp_tac (esimps [setvars_def]) 1)]) ;

val _ = qed_goalw "chst_setvars'" Dvars.thy [chst_def] 
  "((st, nst) : chst vars) = (EX sc. setvars vars sc st = nst)"
  (fn _ => [Safe_tac, 
    (full_simp_tac (esimps [setvars_def] addsplits [split_if_asm]) 2),
    (res_inst_tac [("x", "nst")] exI 1), (rtac ext 1), 
    (full_simp_tac (esimps [setvars_def]) 1), (TRYALL Force_tac)]) ;

val _ = qed_goalw "chst_setvars" Dvars.thy [chst_def] 
  "((st, nst) : chst vars) = (setvars vars nst st = nst)"
  (fn _ => [Safe_tac, (rtac ext 1), (dtac fun_cong 2), 
    (full_simp_tac (esimps [setvars_def] addsplits [split_if_asm]) 2),
    (full_simp_tac (esimps [setvars_def]) 1), (TRYALL Force_tac)]) ;

val _ = qed_goalw "chst_trans" Dvars.thy [trans_def, chst_def]
  "trans (chst vars)" (fn _ => [ Force_tac 1]) ;

val _ = qed_goalw "chst_sym" Dvars.thy [sym_def, chst_def]
  "sym (chst vars)" (fn _ => [ Force_tac 1]) ;

val () = bind_thm ("chst_sym_imp", meta_std (rewrite_rule [sym_def] chst_sym)) ;
val chst_setvarsI' = chst_setvarsI RS chst_sym_imp ;

val _ = qed_goalw "chst_empty" Dvars.thy [diag_def, chst_def]
  "chst {} = diag UNIV" (fn _ => [ (fast_tac (claset () addSIs [ext]) 1)]) ;

val _ = qed_goalw "chst_UNIV" Dvars.thy [chst_def] 
  "chst UNIV = UNIV" (fn _ => [Fast_tac 1]) ;

val _ = qed_goalw_spec_mp "cmd_indep_chst" Dvars.thy [cmd_indep_def] 
  "cmd_indep vars S --> Term t : S s --> (s, t) : chst (-vars)"
  (fn _ => [ Safe_tac, 
    (eres_inst_tac [("x", "s"), ("xa", "s")] allE2 1),
    (full_simp_tac (esimps [mapos.defs]) 1),
    (datac (equalityD1 RS subsetD) 1 1), Clarsimp_tac 1, 
    (rtac (chst_setvarsI RS mem_same) 1), Force_tac 1 ]) ; 


(* prd of indeterminate assignment *)
val _ = qed_goalw "indetass_prd" Dvars.thy 
  [indetass_def, mk_eq chst_UNIV, prdm_def, wlpm_def, o_def]
  "prdm primed (indetass UNIV P) state = ((state, primed) : P)" 
  (fn _ => [Fast_tac 1]) ;

val _ = qed_goal "indetass_trm" Dvars.thy 
  "trmm (indetass vars Q) = (%st. True)" ft_vars ;

(* coercion as described in Lermer, Fidge, Hayes, CATS 2003, pg 60,
  but note, as used in Thm 6.1, condition is on one state (no final state) *)
val _ = qed_goal "indetass_empty" Dvars.thy 
  "(indetass {} Q) = (guard (%st. (st, st) : Q) unitos)" 
  (fn _ => [ (rtac ext 1), (force_tac (cesimps 
      [guard_def, indetass_def, mk_eq chst_empty, unitos_def]) 1)]) ;

(* indeterminate assignment of empty frame *)

(* this is defn on pg 60 of Lermer, Fidge, Hayes, CATS 2003 *)
val _ = qed_goalw "indetass_wlp" Dvars.thy [indetass_def, wlpm_def]
  "wlpm (indetass x Q) R state = \
    \ (ALL primed. (state, primed) : Q Int chst x --> R primed)" fn_at ;

(* or an alternative formulation of indetass_wlp *)
val _ = qed_goal "indetass_wlp'" Dvars.thy 
  "wlpm (indetass x Q) R state = \
    \ (ALL primed. (state, setvars x primed state) : Q --> \
      \ R (setvars x primed state))"
  (fn _ => [ (rtac trans 1), (rtac indetass_wlp 1), Safe_tac, 
    (fast_tac (cis [chst_setvarsI]) 1),
    (dtac (chst_setvars RS iffD1) 1),
    (eres_inst_tac [("x", "primed")] allE 1), Auto_tac]) ;

val _ = qed_goal "indetass_UNIV_wlp" Dvars.thy 
  "wlpm (indetass UNIV Q) R state = ?P"
  (fn _ => [(safe_asm_full_simp_tac (esimps [indetass_wlp, chst_UNIV]) 1),
    rtac refl 1]) ;

(* this is defn on pg 66 of Lermer, Fidge, Hayes, CATS 2003 *)
val _ = qed_goalw "indetass_slp" Dvars.thy [indetass_def, slpm_def]
  "slpm (indetass x Q) R final = \
    \ (EX init. (init, final) : Q Int chst x & R init)" fn_at ;

(* or an alternative formulation of indetass_slp *)
val _ = qed_goal "indetass_slp'" Dvars.thy 
  "slpm (indetass x Q) R primed = \
    \ (EX state. (setvars x state primed, primed) : Q & \
      \ R (setvars x state primed))"
  (fn _ => [ (rtac trans 1), (rtac indetass_slp 1), Safe_tac, 
    (dtac (chst_sym_imp RS (chst_setvars RS iffD1)) 1),
    (res_inst_tac [("x", "init")] exI 1), Asm_simp_tac 1,
    (fast_tac (cis [chst_setvarsI RS chst_sym_imp]) 1) ]) ;

(* this is Thm 5.1 on pg 68 of Lermer, Fidge, Hayes, CATS 2003 *)
val _ = qed_goal "indetass_normal" Dvars.thy 
  "(partcref C (indetass UNIV Q) & partcref (indetass UNIV Q) C) = \
    \ (ALL s d. ((s, d) : Q) = (Term d : C s))"
  (fn _ => [ (simp_tac (esimps [partcref_def, indetass_UNIV_wlp]) 1),
    (simp_tac (esimps [wlpm_def]) 1), Safe_tac, Fast_tac 3, Fast_tac 3,
    (etac thin_rl 2), (chop_tac 1 (etac thin_rl 1)), 
    (REPEAT (EVERY [(etac allE2 1), (etac impE 1), 
      (etac allE 2), (etac impE 2), (atac 2), (atac 2), Fast_tac 1]))]) ;

(* close to Thm 5.3 on page 69 of Lermer, Fidge, Hayes, CATS 2003,
  which relies on the condition, found on top of pg 61, that Q (and W)
  contain, as free primed variables, only those in x' *)
val _ = qed_goalw "indetass_ref" Dvars.thy 
  [indetass_def, partcref_def, liftimp, wlpm_def]
  "partcref (indetass x Q) (indetass x W) = \
    \ (ALL (s, d): chst x. (s, d) : W --> (s, d) : Q)"
  (fn _ => [ Safe_tac, 
    (etac allE 2 THEN etac mp 2), rtac imageI 2, Fast_tac 2,
    (etac allE2 1), (dtac mp 1), 
    (etac allE 2), (dtac mp 2), 
    rtac imageI 2, rtac ImageI 2, Simp_tac 3,
    Fast_tac 2, Clarify_tac 1, (TRYALL atac)]) ;

(* Lemmas in Lermer, Fidge, Hayes, CATS 2003, pg 74-5 *)
val lemA6 = prove_goal Dvars.thy
  "indetass x (Union Qs) = choice (indetass x ` Qs)"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [indetass_def, choice_def]) 1), Fast_tac 1]) ;

val lemA5f = prove_goal Dvars.thy
  "seq (indetass x Q) (indetass x W) st <= indetass x (W O Q) st"
  (fn _ => [ (simp_tac (esimps 
      [indetass_def, seq_def, extos_def, rel_comp_def]) 1),
    Safe_tac, (rtac imageI 1), Simp_tac 1,
    (datac (chst_trans RS transD) 1 1), Fast_tac 1]) ;

val symD = meta_std (sym_def RS defD1) ;

val lemA5b = prove_goal Dvars.thy "Q <= chst x --> \
    \ indetass x (W O Q) st <= seq (indetass x Q) (indetass x W) st"
  (fn _ => [ (simp_tac (esimps 
      [indetass_def, seq_def, extos_def, rel_comp_def]) 1),
    Safe_tac, (rtac UN_I 1), (rtac imageI 2),
    (ALLGOALS (Simp_tac THEN' rtac conjI THEN' atac)),
    (ALLGOALS (datac rev_subsetD 1)),
    (rtac (chst_trans RS transD) 2), 
    (rtac (chst_sym RS symD) 2), ALLGOALS atac]) RS mp ;
  
val _ = qed_goal "ACNFs" Dvars.thy 
  "revert (- vars) A = precon (trmm A) \
    \ (atd (%primed. guard (prds vars primed A) (assignvs vars primed)))"
  (fn _ => [rtac ext 1, rtac set_ext 1, (case_tac "xa" 1), 
    (asm_simp_tac (esimps (mapos.defs :: defs_vars)) 1), 
    (asm_full_simp_tac (esimps (mapos.defs :: defs_vars)) 1), 

    (rtac (imp_disjL RS iffD1) 1), rtac impI 1,
    (REPEAT (etac thin_rl 1)), Safe_tac, 
    (rtac exI 2), (rtac conjI 2), atac 3, 
    (rtac ext 2), (asm_simp_tac (esimps [setvars_def]) 2), Auto_tac]) ;

(* version for total correctness *)
val _ = qed_goalw "NT_revert" Dvars.thy [revert_def]
  "(NonTerm : revert vars A s) = (NonTerm : A s)"
  (fn _ => [ (simp_tac (esimps [mapos.defs]) 1) ]) ;

val NT_precon = rewrite_rule [trmm_def] (precon_trm RS fun_cong) RS
  (sym RS (not_iff RS iffD2) RS not_sym RS (not_iff RS iffD1)) ;

val _ = qed_goalw "ACNFs_tc" Dvars.thy [totceqv_alt]
  "totceqv (revert (- vars) A) (precon (trmm A) \
    \ (atd (%primed. guard (prdts vars primed A) (assignvs vars primed))))"
  (fn _ => [ rtac allI 1, (case_tac "NonTerm : A s" 1),
    (ALLGOALS (asm_simp_tac (esimps [NT_revert, NT_precon, trmm_def]))),
    rtac set_ext 1, (case_tac "x" 1), 
    (clarsimp_tac (cesimps [NT_revert, NT_precon, trmm_def, atd_def]) 1),
    (full_simp_tac (esimps [guard_alt, assignvs_def]) 1),
    (asm_simp_tac (esimps [precon_def, trmm_def]) 1),
    (simp_tac (esimps [atd_def, guard_alt, assignvs_def, revert_def,
      mapos.defs]) 1),
    (rtac iffI 1), (etac ex_forward 1),
    (force_tac (cesimps [prdts_def, wpm_defc]) 1),
    (full_simp_tac (esimps [prdts_def, wpm_defc]) 1), Safe_tac,
    (case_tac "xa" 1), Fast_tac 1, (Clarsimp_tac 1), 
    (etac allE 1), Safe_tac, contr_tac 2, 
    (etac thin_rl 1), (etac swap 1), (rtac ext 1), 
    (force_tac (cesimps [setvars_def]) 1) ]) ;

val _ = qed_goalw_spec_mp "pcompfr_outside_lem" Dvars.thy 
  [pcompfr_def, Let_def, UNION_def]
  "Term nst : pcompfr fS S fT T s --> x ~: (fS Un fT) --> nst x = s x"
  (fn _ => [
    (auto_tac (claset (), esimps [Let_def] addsplits [split_if_asm])) ]) ;

val _ = qed_goalw "allvars_def'" Dvars.thy [allvars_def, chst_def]
  "allvars vars B state = (ALL stm: chst vars `` {state}. B stm)" 
  (fn _ => [ Safe_tac,
    (eres_inst_tac [("x", "stm")] allE 1), 
    (subgoal_tac "setvars vars stm state = stm" 1), 
    (Asm_full_simp_tac 1), 
    (rtac ext 1), (force_tac (cesimps [setvars_def]) 1),
    (etac bspec 1), (simp_tac (esimps [setvars_def]) 1)]) ;

val _ = qed_goal "at_trm" Dvars.thy 
  "trmm (at vars A) = allvars vars (trmm A)"
  (fn _ => [rtac ext 1, Safe_tac, 
    (rewrite_goals_tac [trmm_def, allvars_def,
      at_def, Let_def, revert_def, mk_eq mapNT]),
    (ALLGOALS Force_tac)]) ;

val _ = qed_goal_spec_mp "at_wlpi" Dvars.thy 
  "indep vars Q --> (wlpm (at vars A) Q = allvars vars (wlpm A Q))"
  (fn _ => [rtac impI 1, rtac ext 1, 
    (full_simp_tac (esimps [wlpm_def, allvars_def, mapos_def',
      at_def, Let_def, revert_def, indep_def]) 1),
    Safe_tac, ((case_tac "xa" THEN_ALL_NEW Asm_full_simp_tac) 2),
    (REPEAT (etac allE 2)), (eatac impE 1 2),
    ((etac allE THEN' etac impE) 1),
    rtac image_eqI 1, etac (UNIV_I RS UN_I) 2, Simp_tac 1,
    (ALLGOALS (dtac (chst_setvarsI RSN (2, bspec)))),
    (ALLGOALS Full_simp_tac),
    (TRYALL (eresolve_tac iffDs THEN' atac))]) ;

val _ = qed_goal_spec_mp "at_wlp'" Dvars.thy 
  "wlpm (at vars A) Q st = \
    \ (ALL nst: chst vars `` {st}. wlpm A (Q o setvars vars st) nst)"
  (fn _ => [ 
    (full_simp_tac (esimps [wlpm_def, allvars_def, mapos_def',
      at_def, Let_def, revert_def]) 1), Safe_tac, 
    (etac allE 1), (etac mp 1), 
    ((case_tac "x" THEN_ALL_NEW Asm_full_simp_tac) 2),
    (force_tac (cesimps [chst_setvars]) 2), 
    (full_simp_tac (esimps [image_iff, chst_setvars]) 1), 
    (rtac exI 1), (rtac bexI 1), (eatac ssubst 1 2), Simp_tac 1]) ;

val _ = qed_goal_spec_mp "at_wlp" Dvars.thy 
  "wlpm (at vars A) Q st = \
    \ (ALL nst. wlpm A (Q o setvars vars st) (setvars vars nst st))"
  (fn _ => [ 
    (full_simp_tac (esimps [wlpm_def, mapos_def',
      at_def, Let_def, revert_def]) 1), Safe_tac, 
    (etac allE 1), (etac mp 1), 
    (force_tac (cesimps [image_iff]) 1), 
    ((case_tac "x" THEN_ALL_NEW Asm_full_simp_tac) 1)]) ;

val _ = qed_goalw_spec_mp "at_wlpa" Dvars.thy [allvars_def]
  "wlpm (at vars A) Q st = allvars vars (wlpm A (Q o setvars vars st)) st"
  (fn _ => [ (rtac at_wlp 1) ]) ;

val slps_q = prove_goal Dvars.thy 
  "slps (at vars A) {q} = setvars vars q ` slps A (chst vars `` {q})" 
  (fn _ => [ (rtac set_ext 1), 
    (simp_tac (esimps [slps_def, mapos.defs, 
      at_def, Let_def, revert_def]) 1), Safe_tac,
    (fast_tac (claset () addSIs [chst_setvarsI]) 1),
    (dtac (chst_setvars RS iffD1) 1),
    (rtac exI 1), (rtac conjI 1), (rtac refl 1), 
    (res_inst_tac [("x", "xc")] exI 1), Asm_simp_tac 1]) ;

val _ = qed_goal "at_slps" Dvars.thy
  "slps (at vars A) Qs = (UN q: Qs. setvars vars q ` \
    \ slps A (chst ?vars `` {q}))"
  (fn _ => [ (rtac trans 1), (rtac slps_Un1 1), 
    (simp_tac (esimps [slps_q]) 1)]) ;

val _ = qed_goal "at_slp'" Dvars.thy
  "slpm (at vars A) Q nst = \
    \ (EX st: chst vars `` {nst}. slpm A (Q o setvars vars nst) st)"
  (fn _ => [ 
    (full_simp_tac (esimps [slpm_def, mapos_def',
      at_def, Let_def, revert_def]) 1), Safe_tac, 
    ((case_tac "x" THEN_ALL_NEW Asm_full_simp_tac) 1), 
    (REPEAT_ALL_NEW (ares_tac [exI, bexI, conjI]) 1), Simp_tac 1,
    (rtac ImageI 1), Simp_tac 2, (rtac chst_setvarsI' 1),
    (REPEAT_ALL_NEW (ares_tac [exI, conjI]) 1),
    (simp_tac (esimps [image_iff]) 1),
    (res_inst_tac [("x", "sb")] exI 1), 
    (rtac bexI 1), Simp_tac 2, (dtac chst_sym_imp 1), 
    (asm_full_simp_tac (esimps [chst_setvars]) 1)]) ;

val _ = qed_goal_spec_mp "at_slp" Dvars.thy 
  "slpm (at vars A) Q st = \
    \ (EX nst. slpm A (Q o setvars vars st) (setvars vars nst st))"
  (fn _ => [ 
    (full_simp_tac (esimps [slpm_def, mapos_def',
      at_def, Let_def, revert_def]) 1), Safe_tac, 
    ((case_tac "x" THEN_ALL_NEW Asm_full_simp_tac) 1), 
    (REPEAT (rtac exI 1)), 
    (rtac conjI 1), (etac mem_same 2), (cong_tac 2), 
    (rtac (setvars_same RS sym) 2), Simp_tac 1,
    (REPEAT_ALL_NEW (ares_tac [exI, conjI]) 1),
    (simp_tac (esimps [image_iff]) 1),
    (res_inst_tac [("x", "sb")] exI 1), 
    (rtac bexI 1), (ALLGOALS Simp_tac)]) ;

(** section 10 - parallel composition **)

(* sanity check for definition involving frames - very useful too,
  my first definition was wrong! *)

val _ = qed_goal "pcomp_chk" Dvars.thy
  "pcomp A B = pcompfr UNIV A UNIV B" 
  (fn _ => [ (rtac ext 1), 
    (rewrite_goals_tac [pcompfr_def, Let_def, pcomp_def, pcomprs_def]), 
    (rtac equalityI 1), (ALLGOALS (rtac subsetI)), 
    (ALLGOALS (REPEAT_ALL_NEW (eresolve_tac [UnE, IntE, UN_E]))),
    (case_tac "xa" 1),
    Fast_tac 1, (REPEAT (Fast_tac 2)), 
    rtac UnI2 1, rtac UN_I 1, Fast_tac 1, 
    (asm_simp_tac (simpset () addsimps [Let_def]) 1),
    (etac SigmaE 1), 
    (asm_full_simp_tac (esimps [Let_def] addsplits [split_if_asm]) 1),
    (dtac (fun_cong_all RS iffD2) 1),
    Asm_full_simp_tac 1]) ;

val tacs = [ rtac exI 1, etac conjI 1, rtac ballI 1, 
    (dres_inst_tac [("x", "str")] bspec 1), Fast_tac 1] ; 

val _ = qed_goal "pcompfr_precon" Dvars.thy
  "precon P (pcompfr fA A fB B) = pcompfr fA (precon P A) fB B"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [precon_def, pcompfr_def, Let_def]) 1), Safe_tac]) ;

val _ = qed_goal "pcompfr_revert_lem" Dvars.thy
  "revert (- (fS Un fT)) (pcompfr fS S fT T) = pcompfr fS S fT T"
  (fn _ => [ (rtac ext 1), rewtac revert_def, Safe_tac,
    (case_tac "xa" 2), Safe_tac, (etac mapos.mapos_NT 2),
    (ftac mapos.mapos_T 2), (etac mem_same 2), Simp_tac 2, 

    (etac mapos.elims 1), Fast_tac 1, 
    (rtac mem_same 1), atac 1, Safe_tac,
    (REPEAT (EVERY [
      (rtac ext 1), (clarsimp_tac (cesimps [setvars_def]) 1),
      (dtac pcompfr_outside_lem 1), Fast_tac 1, Force_tac 1])) ]) ;

val prl1 = standard (pcompfr_revert_lem RS arg_cong RS fun_cong) ;
val prl2 = read_instantiate [("f", "totceqv")] prl1 ;

(** prds, prdts, pcompfr - vars analogue of thms in Dmc.ML **)

val _ = qed_goal "pcompfr_prd" Dvars.thy
  "prds (fA Un fB) primed (pcompfr fA A fB B) = \
    \ (prds (fA) primed A && prds (fB) primed B)" 
  (fn _ => [rtac ext 1, 
    (simp_tac (esimps [wlpm_def, prds_def, pcompfr_def, Let_def]) 1), Safe_tac,
    (EVERY tacs), Asm_full_simp_tac 1, (EVERY tacs),
    (force_tac (claset (), esimps [] addsplits [split_if_asm]) 1),
    (REPEAT (ares_tac [exI, conjI, impI] 1)), 
    rtac refl 1, rtac ballI 1, dtac bspec 1, dtac bspec 2, 
    etac trans 3, etac sym 3, Auto_tac]) ;

val _ = qed_goal "trm_or_prdts" Dvars.thy 
  "trmm S s | prdts fr primed S s" ft_vars ;

val _ = qed_goalw "prdts_imp_fis" Dvars.thy [liftimp, prdts_def] 
  "prdts fr primed S ---> fis S"
  (fn _ => [ Auto_tac, (rtac (fis_or_wp RS disjE) 1), Auto_tac ]) ;

val _ = qed_goal "pcompfr_trm" Dvars.thy
  "trmm (pcompfr fA A fB B) = (trmm A && trmm B)" 
  (fn _ => [ rtac ext 1,
    (simp_tac (esimps [trmm_def, pcompfr_def, Let_def]) 1) ]) ;

val _ = qed_goal "pcompfr_prdt" Dvars.thy
  "prdts (fA Un fB) primed (pcompfr fA A fB B) s = \
    \ (trmm A s & trmm B s --> prdts (fA) primed A s & prdts (fB) primed B s)"
  (fn _ => [ (simp_tac (esimps 
      [wpm_def, wlpm_def, trmm_def, prdts_def, pcompfr_def, Let_def]) 1),
    Safe_tac, Fast_tac 3, Fast_tac 3, 
    (TRYALL (EVERY' [rtac exI, etac conjI, Clarify_tac])),
    (case_tac "str : fA" 2), (TRYALL (rtac sym THEN' Force_tac)),

    Full_simp_tac 1, 
    (etac allE 1), (etac thin_rl 1), (etac thin_rl 1), (etac disjE 1), 
    (etac allE 1), (mp_tac 1), (etac allE 1), (etac disjE 1), 
    (etac conjE 1), mp_tac 1, (etac notE 1), (rtac refl 1),
    Force_tac 1, Clarify_tac 1,
    (full_simp_tac (HOL_ss addsplits [split_if_asm]) 1), Auto_tac ]) ;

(* expression for S || T, s6 of Dunne, ZB2002, LNCS 2272, pg 277 *)
val _ = qed_goal "pcompfr_alt" Dvars.thy
  "totceqv (pcompfr fS S fT T) (precon (trmm S && trmm T) (atd (%primed. \
    \ guard (prdts fS primed S && prdts fT primed T) \
    \ (assignvs (fS Un fT) primed))))"
  (fn _ => [ (rtac (prl2 RS iffD1) 1),
    (rtac totceqv_trans 1), (rtac ACNFs_tc 1),
    (simp_tac (esimps [atd_choice, precon_choice_range]) 1),
    (simp_tac (esimps [image_compose RS sym, pcompfr_trm]) 1),
    (rtac totceqv_choice 1), Clarsimp_tac 1,
    (rtac pca_lem 1), (clarsimp_tac (cesimps [pcompfr_prdt]) 1) ]) ; 

val _ = qed_goal "allvars_forallp" Dvars.thy 
  "forallp v B = allvars {v} B"
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [forallp_def, allvars_def]) 1), Safe_tac,
    (eres_inst_tac [("x", "%x. n")] allE 2), 
    (eres_inst_tac [("x", "primed v")] allE 1), 
    (REPEAT (EVERY [(etac rev_iffD1 1), cong_tac 1, rtac ext 1,
      (simp_tac (esimps [setvars_def]) 1)])) ]) ; 

val _ = qed_goalw_spec_mp "chst_mono" Dvars.thy [chst_def]
  "sa <= sb --> chst sa <= chst sb" (fn _ => [Fast_tac 1]) ;

val _ = qed_goalw_spec_mp "indep_mono" Dvars.thy [indep_def]
  "sa <= sb --> indep sb Q --> indep sa Q" 
  (fn _ => [ (strip_tac 1), (dtac chst_mono 1), (Fast_tac 1)]) ;

val _ = qed_goalw "indep_def'" Dvars.thy [indep_def]
  "indep vars Q = (ALL primed st. Q (setvars vars primed st) = Q st)"
  (fn _ => [ (simp_tac (esimps [Ball_def]) 1), Safe_tac,
    (rtac sym 1), (etac allE2 1), (etac mp 1), (rtac chst_setvarsI 1), 
    (full_simp_tac (esimps [chst_setvars]) 1),
    (etac subst 1), Force_tac 1]) ;

val _ = qed_goal "indep_def2" Dvars.thy 
  "indep vars Q = (ALL primed. Q o setvars vars primed = Q)"
  (fn _ => [ (rtac trans 1), (rtac indep_def' 1), 
    (force_tac (claset () addSIs [ext] addSDs [fun_cong], 
      simpset ()) 1)]) ;

val _ = qed_goal_spec_mp "indepD1" Dvars.thy "?P"
  (fn _ => [ (rtac impI 1), (etac (indep_def' RS iffD1) 1) ]) ;

val _ = qed_goalw "indep_pred_upd'" Dvars.thy [pred_upd_def]
  "indep vars Q --> v : vars --> (ALL t. pred_upd Q v t = Q)"
  (fn _ => [ (strip_tac 1), (rtac ext 1),
    (dtac (conjI RS (insert_subset RS iffD2)) 1),
    (rtac empty_subsetI 1), (datac indep_mono 1 1),
    (etac thin_rl 1), (dtac indepD1 1), (rtac trans 1), atac 2,
    (simp_tac (esimps [pred_upd_def, upd_setvars]) 1) ]) ;

val indep_pred_upd2 = insertI1 RSN (2, indep_pred_upd' RS mp RS mp) ;

val _ = qed_goalw_spec_mp "cmd_indep_setvars" Dvars.thy [cmd_indep_def]
  "cmd_indep vars C --> Term nst : C st --> \
    \ Term (setvars vars primed nst) : C (setvars vars primed st)"
  (fn _ => [ (strip_tac 1), (asm_simp_tac (esimps [mapos_def']) 1),
    (dres_inst_tac [("f", "mapo (setvars vars primed)")] imageI 1), 
    (Full_simp_tac 1) ]) ;

val _ = qed_goal_spec_mp "indep_wlp" Dvars.thy 
  "indep vars Q --> cmd_indep vars C --> indep vars (wlpm C Q)"
  (fn _ => [ (strip_tac 1), 
    (simp_tac (esimps [indep_def', wlpm_def]) 1), Safe_tac,
    (datac cmd_indep_setvars 1 1),
    (etac allE 1 THEN eatac impE 1 1), 
    (asm_full_simp_tac (esimps [indep_def']) 1), 
    (dres_inst_tac [("primed", "st")] cmd_indep_setvars 1), atac 1,
    (Full_simp_tac 1), (etac allE 1 THEN etac impE 1), 
    (Full_simp_tac 1), (asm_full_simp_tac (esimps [indep_def']) 1) ]) ; 

val cmd_indep_lem' = prove_goalw Dvars.thy [cmd_indep_def]
  "cmd_indep vars C --> \
    \ (ALL st oc. oc : C st --> mapo (setvars vars st) oc = oc)" 
  (fn _ => [ (strip_tac 1), (etac allE2 1), 
    (subgoal_tac "oc : C (setvars vars st st)" 1), 
    (Asm_simp_tac 2), 
    (dtac set_cong 1), (datac iffD1 1 1), (case_tac "oc" 1), 
    (ALLGOALS (asm_full_simp_tac (esimps [mapos_def', image_def]))), 
    Safe_tac, (case_tac "x" 1), (ALLGOALS (Asm_full_simp_tac)) ]) ;

val _ = qed_goal_spec_mp "cmd_indep_lem" Dvars.thy "?P"
  (fn _ => [ (rtac cmd_indep_lem' 1) ]) ;

val _ = qed_goal_spec_mp "cmd_indep_lemT" Dvars.thy 
  "cmd_indep vars C --> Term nst : C st --> v : vars --> nst v = st v"
  (fn _ => [ (strip_tac 1), (datac cmd_indep_lem 1 1),
    Full_simp_tac 1, (dtac fun_cong 1), (etac (sym RS trans) 1),
    (asm_simp_tac (esimps [setvars_def]) 1) ]) ;

val _ = qed_goal_spec_mp "at_indep" Dvars.thy
  "cmd_indep vars C --> at vars C = C"
  (fn _ => [ (rtac impI 1), (rtac ext 1), 
    (ftac (cmd_indep_lem' RS mp) 1), 
    (full_simp_tac (esimps [cmd_indep_def, at_def, Let_def, revert_def]) 1),
    (subgoal_tac "(UN xa. C (setvars vars xa x)) = \
	\ (UN xa. mapos (setvars vars xa) (C x))" 1), 
    (cong_tac 2), (rtac ext 2), (eatac allE2 1 2), 
    (asm_simp_tac (esimps [mapos_def', image_def]) 1), Safe_tac,
    (simp_tac (esimps [mk_ap mapo_o, setvars_o]) 1), 
    (ALLGOALS (etac allE2 THEN' datac (mp RS sym) 1)), Force_tac 1, 
    (REPEAT (rtac exI 1)), (rtac conjI 1), atac 2, Fast_tac 1 ]) ;

val _ = qed_goal_spec_mp "indep_allvars" Dvars.thy 
  "indep vars (allvars vars Q)" 
  (fn _ => [ (simp_tac (esimps [indep_def', allvars_def]) 1) ]) ;

(** frames **)
val _ = qed_goalw_spec_mp "frame_mono" Dvars.thy [partcref_alt, frame_def]
  "frame A f --> partcref A B --> f <= g --> frame B g" 
  (fn _ => [ Safe_tac, (etac allE 1 THEN datac subsetD 1 1), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "totcref_prdts" Dvars.thy [wpm_def, wlpm_def,
  liftand, liftimp, o_def, totcref_def, prdts_def, Let_def]
  "frame A f --> frame B f --> totcref A B = ((trmm A ---> trmm B) & \
    \ (ALL primed. prdts f primed B ---> prdts f primed A))"
  (fn _ => [ Safe_tac, 
    (eres_inst_tac [("x", "%st. True")] allE 1), Fast_tac 1,
    (etac allE2 1 THEN etac impE 1), (eatac conjI 1 1),
    (etac conjE 1), (etac allE 1 THEN eatac mp 1 1), 
    (etac allE2 1 THEN etac impE 1), Fast_tac 1, Fast_tac 1, 
    (eres_inst_tac [("x", "s"), ("xa", "nst")] allE2 1), Safe_tac,
    Fast_tac 1, (subgoal_tac "nsta ~= nst" 1), Fast_tac 2,
    (etac swap 1 THEN rtac ext 1), (case_tac "x : f" 1), Fast_tac 1,
    rewtac frame_def, (REPEAT (etac allE3 1)),
    (REPEAT (mp_tac 1)), Auto_tac ]) ; 

(** monotonicity **)

(* pcompfr - same frames *)
val _ = qed_goalw_spec_mp "pcompfr_ref_mono_sf" Dvars.thy 
  [gencref_alt, pcompfr_def, Let_def, UNION_def]
  "gencref A1 B1 --> gencref A2 B2 --> \
    \ gencref (pcompfr f1 A1 f2 A2) (pcompfr f1 B1 f2 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [Let_def]) 1), Fast_tac 1]) ;

val _ = qed_goalw_spec_mp "pcompfr_tref_mono_sf" Dvars.thy 
  [totcref_alt, pcompfr_def, Let_def, UNION_def]
  "totcref A1 B1 --> totcref A2 B2 --> \
    \ totcref (pcompfr f1 A1 f2 A2) (pcompfr f1 B1 f2 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [Let_def]) 1), 
    (eres_inst_tac [("x", "s")] allE 1),
    (eres_inst_tac [("x", "s")] allE 1), Safe_tac, 
    (REPEAT_SOME (datac rev_subsetD 1)), TRYALL Fast_tac ]) ;

val _ = qed_goalw_spec_mp "pcompfr_ref_mono" Dvars.thy 
  [gencref_alt, pcompfr_def, Let_def, UNION_def]
  "frame A1 fA1 --> frame A2 fA2 --> fA1 <= fB1 --> fA2 <= fB2 --> \
    \ gencref A1 B1 --> gencref A2 B2 --> \
    \ gencref (pcompfr fA1 A1 fA2 A2) (pcompfr fB1 B1 fB2 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [Let_def]) 1), 
    Safe_tac, Fast_tac 1, Fast_tac 1,
    (ALLGOALS (EVERY' [etac swap, rtac exI, rtac conjI, Fast_tac,
      rtac exI, rtac conjI, etac ball_match_set o incr, Fast_tac o incr,
      rtac impI, rtac conjI, Fast_tac, Simp_tac, rtac ext, Simp_tac ])),
    Safe_tac, (TRYALL (eatac (subsetD RS rev_notE) 2)),
    (TRYALL (REPEAT o
	(datac (meta_std (frame_def RS def_imp_eq RS iffD1)) 1 THEN' Fast_tac)
      THEN' Fast_tac)) ]) ;

val _ = qed_goalw_spec_mp "pcompfr_tref_mono" Dvars.thy 
  [totcref_alt, pcompfr_def, Let_def, UNION_def]
  "frame A1 fA1 --> frame A2 fA2 --> fA1 <= fB1 --> fA2 <= fB2 --> \
    \ totcref A1 B1 --> totcref A2 B2 --> \
    \ totcref (pcompfr fA1 A1 fA2 A2) (pcompfr fB1 B1 fB2 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [Let_def]) 1), 
    (eres_inst_tac [("x", "s")] allE 1),
    (eres_inst_tac [("x", "s")] allE 1), Safe_tac, 
    (REPEAT_SOME (datac rev_subsetD 1)), Fast_tac 1, Fast_tac 1,
    (REPEAT_SOME (etac allE THEN' mp_tac)), 
    (ALLGOALS (full_simp_tac HOL_ss)),
    (REPEAT (EVERY [
      etac allE 1, etac impE 1, atac 1,
      (EVERY [etac allE 1, etac disjE 1, etac notE 2, 
	etac ball_match_set 2, Fast_tac 2]),
      Clarsimp_tac 1, 
      (etac notE 1 THEN rtac ext 1), 
      (full_simp_tac (esimps [frame_def]) 1),
      (SELECT_GOAL Auto_tac 1) ])) ]) ;

