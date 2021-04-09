
structure Dlit = struct val thy = theory "Dlit" end ;
val _ = use_legacy_bindings Dlit.thy ;

(** useful lemmas *)

fun utl() = update_thy "Dlit" ;
fun utol() = update_thy_only "Dlit" ;
fun ul() = use "Dlit.ML" ;

val _ = qed_goal "subLemma" Dlit.thy 
  "expMng (expSub x E Q) state = expMng Q (state (x := expMng E state)) & \ 
  \ expsMng (expsSub x E Qs) state = expsMng Qs (state (x := expMng E state))"
  (fn _ => [ (induct_tac "Q Qs" 1), ALLGOALS Asm_simp_tac]) ;

val _ = qed_goal "subLemma_b" Dlit.thy 
  "bexpMng (bexpSub x E Q) state = bexpMng Q (state (x := expMng E state)) & \ 
    \ bexpsMng (bexpsSub x E Qs) state = \
      \ bexpsMng Qs (state (x := expMng E state))"
  (fn _ => [ (induct_tac "Q Qs" 1), (ALLGOALS Asm_simp_tac),
    (cong_tac 1), (induct_tac "list" 1), 
    (ALLGOALS (asm_simp_tac (esimps [rewrite_rule [fun_upd_def] subLemma])))]) ;

val _ = qed_goal "subLemma_b'" Dlit.thy 
  "bexpMng (bexpSub x E Q) = pred_upd (bexpMng Q) x (expMng E)" 
  (fn _ => [ (rtac ext 1), (rewtac pred_upd_def), 
    (rtac (subLemma_b RS conjunct1) 1)]) ;

val _ = qed_goal "sub_equiv" Dlit.thy 
  "expMng Q = expMng R --> expMng (expSub x E Q) = expMng (expSub x E R)"
  (fn _ => [rtac impI 1, rtac ext 1, 
    (asm_simp_tac (esimps [subLemma]) 1)]) ;

val _ = qed_goal "sub_equiv_b" Dlit.thy 
  "bexpMng Q = bexpMng R --> bexpMng (bexpSub x E Q) = bexpMng (bexpSub x E R)"
  (fn _ => [rtac impI 1, rtac ext 1, 
    (asm_simp_tac (esimps [subLemma_b]) 1)]) ;

(* assignment *)

val _ = qed_goal "ass_wlpl" Dlit.thy
  "wlpm (assigne x (expMng E)) (bexpMng Q) = bexpMng (bexpSub x E Q)" 
  (fn _ => [rtac ext 1,
    (auto_tac (cesimps [wlpm_def, subLemma_b, assigne_def, assignv_def]))]) ; 

(* need assumptions about w not in S or R *)
val _ = qed_goal "var_wlp" Dlit.thy 
  "is S unitos --> \
    \ cmd_indep {w} S --> indep {w} R --> wlpm (at {v} S) R = pred_upd \
    \ (forallp v (wlpm S (pred_upd R v (expMng (Var w))))) w (expMng (Var v))"
  (fn _ => [ (strip_tac 1), (rtac ext 1), 
    (case_tac "v = w" 1), hyp_subst_tac 1, 
    (ftac indep_pred_upd2 1),
    (asm_simp_tac (esimps 
	[at_wlp, allvars_forallp, (indep_allvars RS indep_pred_upd2)]) 1),
    (asm_full_simp_tac (esimps [indep_def2, allvars_def']) 1),
    (force_tac (cesimps [chst_setvars']) 1),
    (* case v ~= w *)
    (simp_tac (esimps [wlpm_def, pred_upd_def, forallp_def]) 1),
    (simp_tac (esimps [at_def, Let_def, revert_def]) 1), Safe_tac,
    (subgoal_tac "nst w = x v" 1), (datac cmd_indep_lemT 1 2),
    (rtac insertI1 2), 
    (full_simp_tac (simpset () addsplits [split_if_asm]) 2),
    (Asm_full_simp_tac 2),
    (eres_inst_tac [("x", "nst(v := x v, w := x w)")] allE 1),
    (etac (tacthm (etac rev_iffD1 3) impE) 1), 
    (full_simp_tac (esimps [Ball_def, chst_def, indep_def]) 2),
    (etac allE2 2), etac mp 2, (Asm_simp_tac 2),
    (* level 22 *)
    (datac cmd_indep_setvars 1 1),
    (subgoal_tac "?t : S (?s (w := x w))" 1), 
    (simp_tac (esimps [upd_setvars]) 2),
    (full_simp_tac (esimps [upd_setvars RS sym, mapos_def', image_def]) 1),
    (res_inst_tac [("x", "%i. n")] exI 1), 
    (res_inst_tac [("x", "Term (nst(w := x w))")] bexI 1), 
    Simp_tac 1, rtac ext 1, (simp_tac (esimps [setvars_def]) 1),
    (etac rev_subsetD 1), (rtac equalityD1 1),
    cong_tac 1, rtac ext 1, (ftac not_sym 1), 
    (asm_simp_tac (esimps [setvars_def]) 1),
    (* level 37 *)
    (full_simp_tac (esimps [mapos_def', image_def]) 1), Safe_tac,
    (case_tac "xa" 1), (ALLGOALS Asm_full_simp_tac),
    (eres_inst_tac [("xa", "a v"), ("x", "s (w := x v)")] allE2 1),
    (etac (tacthm (etac rev_iffD1 3) impE) 1), 
    (asm_full_simp_tac (esimps [indep_def, chst_def]) 2),
    (etac allE2 2), (etac mp 2), 
    (simp_tac (esimps [setvars_def]) 2),
    (dres_inst_tac [("primed", "%i. x v"), ("vars", "{w}")]
      cmd_indep_setvars 1), atac 1,
    (full_simp_tac (esimps [upd_setvars RS sym]) 1),
    (etac rev_subsetD 1), (rtac equalityD1 1),
    cong1_tac 1, rtac ext 1, ftac not_sym 1, 
    (asm_simp_tac (esimps [setvars_def]) 1) ]) ;

