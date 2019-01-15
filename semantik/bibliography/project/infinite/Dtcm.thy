
(* changing to total correctness model *)

theory Dtcm imports Dtc begin 

consts
  magic_tc :: "('s => 's set TorN)"
  abort_tc :: "('s => 's set TorN)"
  precon_tc :: "('s => bool) => ('s => 't set TorN) => ('s => 't set TorN)"
  guard_tc :: "('s => bool) => ('s => 't set TorN) => ('s => 't set TorN)"
  choice_tc :: "('s => 't set TorN) set => ('s => 't set TorN)"
  pcomp_tc :: "('s => 't set TorN) set => ('s => 't set TorN)"
  pc_aux :: "('s => 't set TorN) set => ('s => 't set TorN)"
  concert_tc :: 
    "('s => 't set TorN) => ('s => 't set TorN) => ('s => 't set TorN)"
  pcomprs_tc :: "('t set TorN set) => ('t set TorN)"
  (*
  pcomprs_tc :: "('t set TorN) => ('t set TorN) => ('t set TorN)"
  pcomprs_tc_aux :: "('t set) => ('t set TorN) => ('t set TorN)"
  *)
  trm_tc :: "('s => 't set TorN) => 's => bool"
  fis_tc :: "('s => 't set TorN) => 's => bool"
  wp_tc :: "('s => 't set TorN) => ('t => bool) => 's => bool"
  ref_tc :: "('s => 't set TorN) => ('s => 't set TorN) => bool"
  prd_tc :: "'t => ('s => 't set TorN) => ('s => bool)"
  at_tc :: "('u => 's => 't set TorN) => ('s => 't set TorN)"
  lub_pt :: "(('t => bool) => 's => bool) set => ('t => bool) => 's => bool"
  Qcs :: "('t => bool) => ('t => bool) set" 
  mono_pt :: "(('t => bool) => 's => bool) => bool"
  conj_pt :: "(('t => bool) => 's => bool) => ('t => bool) set => 's => bool"
  gs_of_pt :: "(('t => bool) => 's => bool) => 's => 't set TorN"

defs
  magic_tc_def : "magic_tc s == Term {}"
  abort_tc_def : "abort_tc s == NonTerm"
  precon_tc_def : "precon_tc P C s == if P s then C s else NonTerm"
  guard_tc_def : "guard_tc P C s == if P s then C s else Term {}"
  choice_tc_def : "choice_tc C s == pext_tc (Let s) C"
  concert_tc_def : "concert_tc A B s == 
    case A s of NonTerm => B s | Term Sa => 
      (case B s of NonTerm => Term Sa | Term Sb => Term (Sa Un Sb))"
  trm_tc_def : "trm_tc C s == C s ~= NonTerm"
  fis_tc_def : "fis_tc C s == C s ~= Term {}"
  wp_tc_def : "wp_tc C Q s == EX S. S <= Collect Q & C s = Term S"
  ref_tc_def : "ref_tc A B == ALL Q. wp_tc A Q ---> wp_tc B Q"
  prd_tc_def : "prd_tc primed C == Not o wp_tc C (%st. st ~= primed)"
  pc_aux_def : "pc_aux Cs ==
    (at_tc (%s'. guard_tc (%s. ALL C:Cs. prd_tc s' C s) (%s. Term {s'})))"
  at_tc_def : "at_tc Ad == choice_tc (range Ad)"
  Qcs_def : "Qcs Q == (%y x. x ~= y) ` (- (Collect Q))"
  lub_pt_def : "lub_pt Ts Q x == ALL Q': Qcs Q. EX T:Ts. T Q' x"
  mono_pt_def : "mono_pt T == ALL Q R. (Q ---> R) --> (T Q ---> T R)"
  conj_pt_def : "conj_pt T Qs s == T (%s. ALL Q:Qs. Q s) s = (ALL Q:Qs. T Q s)"
  gs_of_pt_def : "gs_of_pt T == precon_tc (T (%s. True)) 
    (at_tc (%s'. guard_tc (Not o T (%st. st ~= s')) (%s. Term {s'})))" 
  
(*
primrec
  pcomprs_tc_aux_NT : "pcomprs_tc_aux S NonTerm = NonTerm"
  pcomprs_tc_aux_T : "pcomprs_tc_aux S (Term S') = Term (S Int S')"

primrec
  pcomprs_tc_NT : "pcomprs_tc NonTerm T = NonTerm"
  pcomprs_tc_T : "pcomprs_tc (Term S) T = pcomprs_tc_aux S T"

defs
  pcomp_tc_def : "pcomp_tc S T s == pcomprs_tc (S s) (T s)"
*)

defs
  pcomp_tc_def : "pcomp_tc Cs s == pcomprs_tc ((%C. C s) ` Cs)"
  pcomprs_tc_def : "pcomprs_tc rs == if NonTerm : rs then NonTerm
    else Term (Inter (sts_of_ocs rs))"

end

