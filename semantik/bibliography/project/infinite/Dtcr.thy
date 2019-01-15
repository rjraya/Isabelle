
(* repetitive commands, total correctness setting *)

theory Dtcr imports Drc Dtcm begin 

consts
  rep_tc	   :: "'s tccmd => nat => 's tccmd"
  rephat   :: "'s tccmd => 's tccmd"
  repall_tc   :: "'s tccmd => 's tccmd"
  reach_NT   :: "'s tccmd => 's set"
  fprep_tc   :: "'s tccmd => 's tccmd => bool"
  (* section 9, 9.1 *)
  while_tc   :: "('s => bool) => 's tccmd => 's tccmd"
  if_tc   :: "('s => bool) => 's tccmd => 's tccmd => 's tccmd"
  ifthen_tc   :: "('s => bool) => 's tccmd => 's tccmd"
  loop_tc    :: "'s tccmd"
  treach :: "'s tccmd => 's => 's set"
  breach :: "'s tccmd => 's => 's set"
  infchs_tc :: "'s tccmd => 's set"
  icnt_tc :: "'s tccmd => 's set"
  isuc_tc :: "'s tccmd => 's => 's"
  infch_of_tc :: "'s tccmd => 's => (nat => 's)"

primrec
  rep_tc_0 : "rep_tc C 0 = unit_tc" 
  rep_tc_Suc : "rep_tc C (Suc n) = seq_tc C (rep_tc C n)" 

coinductive "infchs_tc C"
  intros
    I : "[| C s = Term S ; ns : S ; ns : infchs_tc C |] ==> s : infchs_tc C"

(* infinite chain or reaches NonTerm *)
coinductive "icnt_tc C"
  intros
    icI : "[| C s = Term S ; ns : S ; ns : icnt_tc C |] ==> s : icnt_tc C"
    NTI : "C s = NonTerm ==> s : icnt_tc C"

defs
  isuc_tc_def : "isuc_tc C s == SOME ns. 
    (EX S. C s = Term S & ns : S) & ns : infchs_tc C"
  infch_of_tc_def : "infch_of_tc C s == nat_rec s (%n. isuc_tc C)"

(* treach, breach :: "'a tccmd => 'a tccmd"
  inductive approach to while loops:
  returns set of states reachable from initial state by iterating C,
  second version for backward reachability, which we will prove equivalent *)

inductive "treach C s0"
  intros
    tr_0 : "s0 : treach C s0"
    tr_Suc : "[| C s = Term S ; sf : S ; s : treach C s0 |] ==>
      sf : treach C s0" 

inductive "breach C s0"
  intros
    br_0 : "s0 : breach C s0"
    br_Suc : "[| C sf = Term S ; s : S ; s : breach C s0 |] ==>
      sf : breach C s0" 

(* set of states from which NonTerm is reachable *)
inductive "reach_NT C"
  intros
    I_0 : "C s = NonTerm ==> s : reach_NT C"
    I_Suc : "[| C s = Term S ; ns : S ; ns : reach_NT C |] ==> s : reach_NT C"

defs
  rephat_def : "rephat C state ==
    if state : icnt_tc C then NonTerm else Term (treach C state)"
  repall_tc_def : "repall_tc C state == 
    if state : reach_NT C then NonTerm else Term (treach C state)"

  fprep_tc_def  : "fprep_tc A X == X = choice_tc {seq_tc A X, unit_tc}"

  if_tc_def :
    "if_tc Gm A B == choice_tc {guard_tc Gm A, guard_tc (Not o Gm) B}"
  ifthen_tc_def :
    "ifthen_tc Gm A == choice_tc {guard_tc Gm A, guard_tc (Not o Gm) unit_tc}"
  while_tc_def  : "while_tc Gm A ==
    seq_tc (rephat (guard_tc Gm A)) (guard_tc (Not o Gm) unit_tc)"
  loop_tc_def   : "loop_tc == while_tc (%s. True) unit_tc"

end
