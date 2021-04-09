
structure Dcmd = struct val thy = theory "Dcmd" end ;
val _ = use_legacy_bindings Dcmd.thy ;

fun utc() = update_thy "Dcmd" ;
fun utoc() = update_thy_only "Dcmd" ;
fun uc() = use "Dcmd.ML" ;

val defs_cmd = wp'_def :: wlp'_def :: trm'_def :: F_def :: T_def :: defs_mc ; 

val cs_cmd = cesimps defs_cmd ;

fun ft_cmd _ = [REPEAT (resolve_tac [ext, impI] 1), auto_tac cs_cmd] ;

(*** section 4 ***)

(** assignment **)

val Skip_def' = prove_goal Dcmd.thy "cmdMng Skip = unitos" ft_cmd ;

val Ass_trm = prove_goal Dcmd.thy 
  "trm' (x ::= E) state = True" ft_cmd ;

val Ass_wlp = prove_goal Dcmd.thy 
  "wlp' (x ::= E) Q = bexpMng (bexpSub x E Q)" 
  (fn _ => [ rtac ext 1,
    (simp_tac (esimps [wlp'_def, wlpm_def, subLemma_b]) 1)]) ;

(** preconditioned command **)

val Precon_wlp = prove_goal Dcmd.thy 
  "wlp' (Precon bexp cmd) = wlp' cmd" ft_cmd ;

val Precon_trm = prove_goal Dcmd.thy 
  "trm' (Precon bexp cmd) state = (bexpMng bexp state & trm' cmd state)"
  ft_cmd ;

val PC_trm = prove_goal Dcmd.thy
  "bexpMng pc = trm' A --> cmdMng (Precon pc A) = cmdMng A" ft_cmd ;

(* intuition about Precon - allows non-termination when condition fails *)

val PC_nonterm = prove_goalw Dcmd.thy [Abort_def, Magic_def]
  "cmdMng (Precon C A) = (cmdMng (BC A (BRel notf [C] -> Abort)))" ft_cmd ;

(** guarded command **)

val Guard_wlp = prove_goal Dcmd.thy 
  "wlp' (bexp -> cmd) Q state = (bexpMng bexp state --> wlp' cmd Q state)" 
  ft_cmd ;

val Guard_trm = prove_goal Dcmd.thy 
  "trm' (bexp -> cmd) state = (bexpMng bexp state --> trm' cmd state)" ft_cmd ;

(** sequential composition **)

val Seq_wlp = prove_goal Dcmd.thy 
  "bexpMng wbq = wlp' B Q --> wlp' (Seq A B) Q = (wlp' A wbq)" 
  (fn _ => [(rtac impI 1), (rtac ext 1),
    (asm_simp_tac (esimps defs_cmd) 1),
    Safe_tac, (Force_tac 1),
    (case_tac "xa" 1), (Auto_tac)]) RS mp ;

val Seq_trm = prove_goal Dcmd.thy "bexpMng trmB = trm' B --> \
    \ trm' (Seq A B) state = (trm' A state & wlp' A trmB state)" 
  (fn _ => [ (rtac impI 1),
    (asm_simp_tac (esimps defs_cmd) 1),
    Safe_tac, (case_tac "x" 3), Auto_tac]) RS mp ;

(** section 5.1 **)

(* Magic is the everywhere infeasible command *)
val Magic = prove_goalw Dcmd.thy [Magic_def]
  "cmdMng Magic state = {}" ft_cmd ;

(* actually (false -> A) would be just as good a definition for Magic *)
val Magic_alt = prove_goalw Dcmd.thy [Magic_def] 
  "cmdMng Magic = cmdMng (F -> Skip)" ft_cmd ;

(* Abort is the command that never terminates *)
val Abort = prove_goalw Dcmd.thy [Abort_def, Magic_def]
  "cmdMng Abort state = {NonTerm}" ft_cmd ;

(* change rules for unitos to cmdMng Skip *)
val [ext2o_Skip, seq_SkipL, seq_SkipR, rep_Skip] =
  map (fold_rule [mk_eq Skip_def'] o transfer Dcmd.thy) 
  [ext2o_unit, seq_unitL, seq_unitR, rep_unit] ;

(* alternative formulation of Abort as infinite loop *)
val AbortIsLoop = prove_goalw Dcmd.thy [Abort_def, Magic_def]
  "cmdMng Abort = cmdMng (while T do Skip end)" 
  (fn _ => [ (rtac ext 1), (auto_tac (cesimps (infch_def :: defs_cmd))) ]) ;
    
(* Perhaps may terminate as no-op, or not terminate *)
val Perhaps = prove_goalw Dcmd.thy [Perhaps_def]
  "cmdMng Perhaps state = {NonTerm, Term state}" ft_cmd ;

(*** section 6 ***)

(** bounded choice **)

val BC_wlp = prove_goalw Dcmd.thy [wlp'_def, wlpm_def] 
  "wlp' (BC A B) Q state = (wlp' A Q state & wlp' B Q state)" ft_cmd ;

val BC_trm = prove_goal Dcmd.thy 
  "trm' (BC A B) state = (trm' A state & trm' B state)" ft_cmd ;

val BC_Magic = prove_goalw Dcmd.thy [Magic_def]
  "cmdMng (BC A Magic) = cmdMng A" ft_cmd ;

(** section 8.2 **)

(* RepClos cmd is a fixed point
val isfp = prove_goal Dcmd.thy
  "cmdMng (RepClos A) = cmdMng (BC (A ;; RepClos A) Skip)"
  (fn _ => [ rtac ext 1,
    (simp_tac (esimps defs_cmd delsimps [seq_def]) 1), Safe_tac, 
    *)

(*** section 9 ***)

val ITE_def = prove_goal Dcmd.thy
  "cmdMng (ITE G A B) = cmdMng (BC (Guard G A) (Guard (BRel notf [G]) B))"
  ft_cmd ;

val IT_def = prove_goal Dcmd.thy
  "cmdMng (IT G A) = cmdMng (BC (Guard G A) (Guard (BRel notf [G]) Skip))"
  ft_cmd ;

(*** section 10 ***)

(** Concert **)

val Conc_wlp = prove_goal Dcmd.thy 
  "wlp' (A ## B) Q state = (wlp' A Q state & wlp' B Q state)" ft_cmd ;

val Conc_trm = prove_goal Dcmd.thy 
  "trm' (A ## B) state = (trm' A state | trm' B state)" ft_cmd ;

(** changing possibility of non-termination **)

val Conc_Magic = prove_goalw Dcmd.thy [Magic_def]
  "cmdMng (A ## Magic) state = cmdMng A state - {NonTerm}" ft_cmd ;

val BC_Abort = prove_goalw Dcmd.thy [Magic_def, Abort_def]
  "cmdMng (BC A Abort) state = cmdMng A state Un {NonTerm}" ft_cmd ;

(** re Egli-Milner ordering **)

(* (BC A Abort) <=em A *)

val em_BC_Abort = prove_goalw Dcmd.thy 
  [EgMil_def, totcref_def, partcref_def, wpm_def, Magic_def, Abort_def]
  "EgMil (BC A Abort) A" ft_cmd ;
  
(* A <=em (A ## Magic), for the same reason, ie the difference is only
  the likelihood of non-termination *)

val em_Conc_Magic = prove_goalw Dcmd.thy 
  [EgMil_def, totcref_def, partcref_def, wpm_def, Magic_def, Abort_def]
  "EgMil A (A ## Magic)" ft_cmd ;

val rc = prove_goal Dcmd.thy "cmdMng (RepClos cmd) = repstar (cmdMng cmd)"
  (fn _ => [rtac ext 1, Simp_tac 1]) ;

(* RepClos cmd is a fixed point of X = (A ; X) [] Skip *)
val RepClos_isfp = prove_goal Dcmd.thy
  "cmdMng (RepClos A) = cmdMng (BC (A ;; RepClos A) Skip)"
  let val th = rewrite_rule [mk_eq fprep_alt] repstar_isfp ;
  in (fn _ => [ rtac ext 1,
    (simp_tac (esimps [th, rc, choice_def]) 1)]) end ;

(* consistency of formulae for wlp with that for wlpm *)
(*  I don't think we can do this because we can't express
  wlp in terms of literal expressions, for some commands like RepClos 
val () = qed_goal "wlp_wlpm" Dcmd.thy
  "ALL R. bexpMng (wlp C R) = wlpm (cmdMng C) (bexpMng R)"
  (fn _ => [ (induct_tac "C" 1), Safe_tac, 
    (TRYALL (rtac ext)), 
    (asm_simp_tac (esimps [wlpm_def]) 1),
    (asm_simp_tac (esimps [seq_wlp]) 1),
    (asm_simp_tac (esimps [wlpm_def, subLemma_b]) 1),
    (asm_simp_tac (esimps [wlpm_def]) 1),
    (asm_simp_tac (esimps [wlpm_def]) 1),
    (* While *)
    (asm_simp_tac (esimps [guard_wlp]) 2),
    (asm_simp_tac (esimps [precon_wlp]) 2),
    (* Pcomp *)
    (asm_simp_tac (esimps [choice_wlp]) 3),
*)
