
(* repetitive commands *)

theory Drc imports Dmc begin

consts
  repall :: "'s acmd => 's acmd"
  repstar   :: "'s acmd => 's acmd"
  fprepst   :: "'s acmd => 's acmd => 's => bool"
  fprep   :: "'s acmd => 's acmd => bool"
  (* section 9, 9.1 *)
  while :: "('s => bool) => 's acmd => 's acmd"
  ifthen   :: "('s => bool) => 's acmd => 's acmd"
  loop    :: "'s acmd"

defs
  repall_def : "repall C state == UN n. rep n C state"
  repstar_def : "repstar C state == repall C state Un 
      (if infch C state then {NonTerm} else {})"
  fprepst_def :  "fprepst A X state == 
    X state = seq A X state Un {Term state}"
  fprep_def :  "fprep A X == ALL state. fprepst A X state"

  ifthen_def :  "ifthen Gm A == choice {guard Gm A, guard (Not o Gm) unitos}"
  while_def :  "while Gm A ==
    seq (repstar (guard Gm A)) (guard (Not o Gm) unitos)"
  loop_def :   "loop == while (%s. True) unitos"

end
