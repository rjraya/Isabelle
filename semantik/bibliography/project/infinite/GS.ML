
structure GS = struct val thy = theory "GS" end ;
val _ = use_legacy_bindings GS.thy ;

(* proofs and definitions specifically to do with
  Steve Dunne. A Theory of Generalised Substitutions.  ZB 2002, LNCS 2272 *)

(* note - in paper, talk about coinductive definition of infchs *)

(* Table 1, pg 274 *)
[ass_wp_tc, precon_wp_tc, guard_wp_tc, choice_wp_tc, seq_wp_tc] ;

(* Table 2, def'ns of abort, magic, pg 275 *)
[magic_tc_def, magic_alt, abort_tc_def, abort_alt] ;

(* s5, pg 276 *)
[trm_alt] ;
(* pg 277 *)
[pc_trm_tc, fis_alt, fis_guard_tc] ;


(* s6, pg 277, bottom *)
(* results where frame is whole state *)
[pcomp_tc_alt, trm_pcomp_tc, prd_pcomp_tc, prd_pcomp_tc2] ; 

(* s6.1, pg 278 *)
[pcomp_choice_tc] ;

(* s7, pg 278 *)
(* bottom, expression for lub of GSs, when frame is whole state *)
[lub_tc] ;

(* monotonicity of various things *) (* done in fgs paper *)
[pcomp_tc_ref_mono, seq_tc_ref_mono, choice_tc_ref_mono,
  precon_tc_ref_mono, guard_tc_ref_mono] ;
[repall_tc_ref_mono, rephat_ref_mono] ;

(* s8.2, pg 279 shows rephat as defined is the lfp *)
[rephat_isfp, rephat_is_lfp] ; (* done in fgs paper *)

(* pg 281, while
  while_def is def'n in paper
  while_prog shows equivalence to intuitive definition *)
[while_tc_def, while_tc_prog] ;  (* done in fgs paper *)

(* pg 282, GS2 *)
[wp_tc_gen_conj] ;

(* done to here in fgs paper *)

(* s6, pg 277, bottom *)
(* results where frame is not whole state *)
[pcompfr_alt, pcompfr_trm, pcompfr_prdt] ;

(* s7.1, pg 279 *)
(* monotonicity of || without, with frame inclusion *)
[pcompfr_tref_mono] ;

(* pg 282, GS3 *)
(* wrong to use cmd_indep, should use frame_tc *)
[GS3] ; (* in fgs paper *)

(* pg 283, s10.2, Prop'n 1, monotonicity proved from conjunctivity,
  and weak conjunctivity proved from monotonicity *)
[wpm_mono_cond_alt, wpm_weak_disj] ;
 
(* pg 284, Prop'n 2 *)
[trm_or_prd_tc, prd_tc_imp_fis, fis_or_wp_tc, wp_imp_trm_tc] ;
(* in fgs paper *)

[trm_or_prdf_tc, prdf_tc_imp_fis] ;

(* pg 285, Prop'n 3; note that for frame (S) \ R,
  we say that S does not change the R-status of the state *)
(* following is equivalent for general correctness *)
val _ = qed_goal "prop3_gc" Dmng.thy 
  "(ALL s' s. Term s' : S s --> (R s' = R s)) --> \
    \ wpm S (Q V R) = (wpm S Q V (trmm S && R))"
  (fn _ => [ (safe_tac (cis [ext])),
    (auto_tac (cesimps [wpm_def, wlpm_def, trmm_def])) ]) ;

(* pg 286, Prop'n 4; first, assume frame (S) = all vars;
  second, rather than assume frame (S) = s,
  modify result to deal with vars outside s modified by S *)
[ACNF_tc, ACNFs_tc] ;

(* pg 286, Prop'n 5; we refer to revert (-s) S 
  which does not change variables outside s *)

val _ = qed_goalw "prop5_gc" GS.thy [prdts_def]
  "prdts y p (revert (-s) S) st = (prdts (y Int s) p S st & \
    \ (trmm S st --> (ALL x: y - s. p x = st x)))"
  (fn _ => [ (simp_tac (esimps [wpm_defc, trmm_def]) 1),
    (simp_tac (esimps [revert_def, mapos.defs]) 1), 
    Safe_tac, (TRYALL Fast_tac), 
    (force_tac (cesimps [setvars_def]) 1),
    (force_tac (cesimps [setvars_def]) 1),

    (case_tac "x" 1), Force_tac 1, 
    (dtac subsetD 1), Simp_tac 1, rtac disjI2 1, rtac exI 1,
    (rtac conjI 1), rtac refl 1, Fast_tac 1, 
    (full_simp_tac (esimps [setvars_def] addsplits [split_if_asm]) 1),
    TRYALL Force_tac ]) ;

(* pg 287, Prop'n 7  *)
[ref_tc_prdt (* only for prd_tc, in fgs paper *),
  totcref_prdts (* prdts for same frame *) ] ;

(* pg 288, Prop'n 7 (the second one!)  *)
[choice_ref_tc] ;
    



