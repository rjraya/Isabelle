

theory Dmc imports Dmng begin 

consts
  conc      :: "[('s, 't) vacmd, ('s, 't) vacmd] => ('s, 't) vacmd"
  pcomp      :: "[('s, 't) vacmd, ('s, 't) vacmd] => ('s, 't) vacmd"

  (* the following act only on whole states *)
  atd     :: "('u => ('s, 't) vacmd) => ('s, 't) vacmd"
  prdtm :: "'t => ('s, 't) vacmd => 's => bool"
  prdm :: "'t => ('s, 't) vacmd => 's => bool"

  guard	   :: "('s => bool) => ('s, 't) vacmd => ('s, 't) vacmd"
  precon	   :: "('s => bool) => ('s, 't) vacmd => ('s, 't) vacmd"
  rep	   :: "nat => 's acmd => 's acmd"
  concrs :: "'st TorN set => 'st TorN set => 'st TorN set"
  pcomprs :: "'st TorN set => 'st TorN set => 'st TorN set"
  wreach :: "'s acmd => 's acmd"
  wrrel  :: "'s acmd => 's acmdrel"
  fis :: "'s acmd => 's => bool"
  abt :: "'s acmd => 's => bool"
  cic :: "'s acmd => 's => bool"
  infch :: "'s acmd => 's => bool"
  saf :: "'s acmd => 's => bool"
  infchs :: "'s acmd => 's set"
  icnt :: "'s acmd => 's set"
  isuc :: "'s acmd => 's => 's"
  infch_of :: "'s acmd => 's => (nat => 's)"
  choice  :: "('a, 'b) vacmd set => ('a, 'b) vacmd"
  r2c :: "('a * 'b) set => 'a => 'b set"
  c2r :: "('a => 'b set) => ('a * 'b) set"

defs 
  r2c_def : "r2c r a == r `` {a}"
  c2r_def : "c2r f == {(a, b). b : f a}"

primrec
  rep_0 : "rep 0 C = unitos" 
  rep_Suc : "rep (Suc n) C = seq C (rep n C)" 

defs
  prdm_def : "prdm primed A == Not o wlpm A (%st. st ~= primed)"
  (* corresponding notion for total correctness, Dunne, ZB2002 *)
  prdtm_def : "prdtm primed A == Not o wpm A (%st. st ~= primed)"
  pcomprs_def : "pcomprs cr1 cr2 == 
      (cr1 Int cr2) Un ({NonTerm} Int (cr1 Un cr2))"
  concrs_def : "concrs cr1 cr2 == 
      ((cr1 Un cr2) - {NonTerm}) Un ({NonTerm} Int cr1 Int cr2)"
  pcomp_def : "pcomp A B state == pcomprs (A state) (B state)"
  conc_def : "conc A B state == concrs (A state) (B state)"
  guard_def : "guard P C state == if P state then C state else {}"
  precon_def : "precon P C state == 
    if P state then C state else insert NonTerm (C state)"

defs
  (* the sort of at used in ACNF, namely where the indeterminate variables
    are from a shadow (primed) state *)
  atd_def : "atd Ad state == UN primed. (Ad primed state)"

  fis_def : "fis C state == C state ~= {}"
  abt_def : "abt C state == C state = {NonTerm}"
  cic_def : "cic C state == (ALL n. fis (rep n C) state)"
  infch_def : "infch C state == 
    (EX f. f 0 = state & (ALL n. Term (f (Suc n)) : C (f n)))"
  saf_def : "saf C state == (ALL n. trmm (rep n C) state)"

coinductive "infchs A"
  intros
    I : "Term ns : A s ==> ns : infchs A ==> s : infchs A"

(* when NonTerm is in repstar A *)
coinductive "icnt A"
  intros
    icI : "Term ns : A s ==> ns : icnt A ==> s : icnt A"
    NTI : "NonTerm : A s ==> s : icnt A"

defs
  isuc_def : "isuc A s == SOME ns. Term ns : A s & ns : infchs A"
  infch_of_def : "infch_of A s == nat_rec s (%n. isuc A)"

defs
  (* choice  :: "('a, 'b) vacmd set => ('a, 'b) vacmd"
    choose, arbitrarily, from set of commands *)
  choice_def : "choice cms state == UNION cms (%C. C state)"

(* wreach :: "'a acmd => 'a acmd"
  wrrel  :: "'s acmd => 's acmdrel"
  inductive approach to while loops:
  returns set of states reachable from initial state by iterating C,
  two alternative versions which we will prove equal *)

inductive "wreach C s0"
  intros
    wr_0 : "Term s0 : wreach C s0"
    (* form of rule makes inductive proof of wreach_rel much easier *)
    wr_Suc : "[| cr : C s ; oc = Term s ; oc : wreach C s0 |] ==>
      cr : wreach C s0" 

inductive "wrrel C"
  intros
    wr_0 : "(s0, Term s0) : wrrel C"
    wr_Suc : "[| (s, cr) : wrrel C ; Term s : C s0 |] ==>
      (s0, cr) : wrrel C" 
    (* need third clause to allow non-terminating outcome *)
    wr1 : "cr : C s ==> (s, cr) : wrrel C"

end

