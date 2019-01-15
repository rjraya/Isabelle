
(* changing to total correctness model *)

theory Dtc imports Dmc Cnv begin 

types
  'a tccmd = "'a => 'a set TorN"
  ('a, 'b) vtccmd = "'a => 'b set TorN"

consts
  swap_tc :: "'s TorN set => 's set TorN"
  unit_tc :: "('s => 's set TorN)"
  prodtc :: "'s set TorN set => 's set TorN" 
  ext_tc :: "('a => 'b set TorN) => 'a set TorN => 'b set TorN"
  pext_tc :: "('a => 'b set TorN) => 'a set => 'b set TorN"
  maptc :: "('a => 'b) => 'a set TorN => 'b set TorN"
  seq_tc :: "('a, 'b) vtccmd => ('b, 'c) vtccmd => ('a, 'c) vtccmd"

defs
  swap_tc_def : "swap_tc ocs == 
    if NonTerm : ocs then NonTerm else Term (sts_of_ocs ocs)"
  unit_tc_def : "unit_tc s == Term {s}"
  seq_tc_def : "seq_tc A B == ext_tc B o A"
  prodtc_def : "prodtc S == 
    if NonTerm : S then NonTerm else Term (Union (sts_of_ocs S))"
  pext_tc_def : "pext_tc f == prodtc o image f"
  ext_tc_def : "ext_tc == exto o pext_tc"
  
primrec
  maptc_NT : "maptc f NonTerm = NonTerm"
  maptc_Term : "maptc f (Term S) = Term (f ` S)"
  
end

