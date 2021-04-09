
structure Dac = struct val thy = theory "Dac" end ;
val _ = use_legacy_bindings Dac.thy ;

(*
AddSIs (liftoc.intros) ;
Addsimps [liftoc.INT] ;

val _ = qed_goal "trmm_liftst1" Dac.thy "trmm (liftst1 A) = trmm A o fst"
  (fn _ => [ (rtac ext 1), Safe_tac,
    (auto_tac (cesimps [trmm_def, mapNT]))]) ;

val _ = qed_goal "trmm_liftst2" Dac.thy "trmm (liftst2 A) = trmm A o snd"
  (fn _ => [ (rtac ext 1), Safe_tac,
    (auto_tac (cesimps [trmm_def, mapNT]))]) ;
*)

val [fwdinit_def', fwdrefg_def', bwdinit_def', bwdrefg_def'] = 
  map (rewrite_rule [fwdrefg_def, bwdrefg_def])
    [fwdinit_def, fwdrefg_def, bwdinit_def, bwdrefg_def] ; 

Delrules [rel_compE] ; AddSEs [rel_compEpair] ;

(* does this relationship respect composition ?
  yes, because the composition A1 ; A2 is given by
  svf2rel (A1 ; A2) = svf2rel A2 O svf2rel A1 *)

val _ = qed_goalw "arp_rel" Dac.thy [arp_def, wpom_def, cnjg_def, o_def]
  "arp A R (a, c) = ((a, c) : Collect R O svf2rel A)" fn_at ;

val _ = qed_goalw "rcp_rel" Dac.thy [rcp_def, spom_def]
  "rcp C R (a, c) = ((a, c) : svf2rel C O Collect R)" fn_at ;

val _ = qed_goalw_spec_mp "fwdrefg_seq" Dac.thy [fwdrefg_def, sseq_def]
  "fwdrefg A1 C1 R S --> fwdrefg A2 C2 S T --> \
    \ fwdrefg (sseq A1 A2) (sseq C1 C2) R T"
  (fn _ => [ (simp_tac (esimps [arp_rel, rcp_rel]) 1), Safe_tac,
    (REPEAT (EVERY [(etac allE2 1), (etac impE 1),
      (fast_tac (cis [rel_compI]) 1)])), Fast_tac 1]) ;

val _ = qed_goalw_spec_mp "fwdref2a_seq" Dac.thy [fwdref2a_def]
  "fwdref2a A1 C1 R --> fwdref2a A2 C2 R --> \
    \ fwdref2a (sseq A1 A2) (sseq C1 C2) R"
  (fn _ => [ Safe_tac, (eatac fwdrefg_seq 1 1) ]) ;

val _ = qed_goalw "rap_rel" Dac.thy [rap_def, spom_def]
  "rap A R (a, c) = ((a, c) : Collect R O converse (svf2rel A))" fn_at ;

val _ = qed_goalw "crp_rel" Dac.thy [crp_def, wpom_def, cnjg_def, o_def]
  "crp C R (a, c) = ((a, c) : converse (svf2rel C) O Collect R)" fn_at ;

val _ = qed_goalw_spec_mp "bwdrefg_seq" Dac.thy [bwdrefg_def, sseq_def]
  "bwdrefg A1 C1 R S --> bwdrefg A2 C2 S T --> \
    \ bwdrefg (sseq A1 A2) (sseq C1 C2) R T"
  (fn _ => [ (simp_tac (esimps [rap_rel, crp_rel]) 1), Safe_tac,
    (REPEAT (EVERY [(etac allE2 1), (etac impE 1),
      (fast_tac (cis [rel_compI]) 1)])), Fast_tac 1]) ;

val _ = qed_goalw_spec_mp "bwdref2a_seq" Dac.thy [bwdref2a_def]
  "bwdref2a A1 C1 R --> bwdref2a A2 C2 R --> \
    \ bwdref2a (sseq A1 A2) (sseq C1 C2) R"
  (fn _ => [ Safe_tac, (eatac bwdrefg_seq 1 1) ]) ;

val _ = qed_goalw_spec_mp "fwdinit_rel" Dac.thy [fwdinit_def']
  "fwdinit (%a. inita) (%c. initc) R = (initc <= (Collect R `` inita))"
  (fn _ => [ (force_tac (cds [subsetD], esimps [arp_rel, rcp_rel]) 1) ]) ;

val _ = qed_goalw_spec_mp "bwdinit_rel" Dac.thy [bwdinit_def']
  "bwdinit (%a. inita) (%c. initc) R = \
    \ ((converse (Collect R) `` initc) <= inita)"
  (fn _ => [ (force_tac (cds [subsetD], esimps [rap_rel, crp_rel]) 1) ]) ;

val _ = qed_goalw_spec_mp "fwdinit_seq" Dac.thy [fwdinit_def, fwdref2a_def]
  "fwdinit AI CI R --> fwdref2a A C R --> fwdinit (sseq AI A) (sseq CI C) R"
  (fn _ => [ Safe_tac, (eatac fwdrefg_seq 1 1) ]) ;

val _ = qed_goalw_spec_mp "bwdinit_seq" Dac.thy [bwdinit_def, bwdref2a_def]
  "bwdinit AI CI R --> bwdref2a A C R --> bwdinit (sseq AI A) (sseq CI C) R"
  (fn _ => [ Safe_tac, (eatac bwdrefg_seq 1 1) ]) ;






