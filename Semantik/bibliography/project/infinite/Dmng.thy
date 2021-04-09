

theory Dmng imports HOL_Gen begin 

types
  ('string, 'nat) state = "'string => 'nat"

(** lifting of logical operators **)

consts
  "&&"      :: "['s => bool, 's => bool] => 's => bool"    (infixr 35)
  "V"      :: "['s => bool, 's => bool] => 's => bool"    (infixr 30)
  "---->"  :: "['s => 't => bool, 's => 't => bool] => bool" (infixr 20)

defs
  liftand : "(p && q) s == p s & q s"
  dlidef : "T ----> U == ALL Q. T Q ---> U Q"
  liftor  : "(p V q) s == p s | q s"

(** switching between relations and set-valued functions **)

consts
  svf2rel :: "('s => 't set) => ('s * 't) set"
  rel2svf :: "('s * 't) set => ('s => 't set)"
  revsvf :: "('s => 't set) => ('t => 's set)"

inductive "rel2svf r s"
  intros
    I : "(s, t) : r ==> t : rel2svf r s"
    
inductive "svf2rel f"
  intros
    I : "t : f s ==> (s, t) : svf2rel f"
    
inductive "revsvf f t"
  intros
    I : "t : f s ==> s : revsvf f t" 

(** monadic stuff - compound monad, of set monad and exception monad **)

datatype 's TorN = NonTerm | Term "'s"

types 
  ('s, 't) vacmd = "'s => 't TorN set"
  's acmd = "'s => 's TorN set"
  (* command as relation rather than set-valued function *)
  's acmdrel = "('s * 's TorN) set"
  ('n, 'v) cmdMngTy = "('n, 'v) state acmd"
  ('n, 'v) expMngTy = "('n, 'v) state => 'v"
  ('n, 'v) bexpMngTy = "('n, 'v) state => bool"

consts
  unitos :: "'s => 's TorN set"
  magic :: "'s => 's TorN set"
  abort :: "'s => 's TorN set"
  perhaps :: "'s => 's TorN set"
  mapo   :: "('s => 't) => ('s TorN => 't TorN)"
  mapos   :: "('s => 't) => ('s TorN set => 't TorN set)"
  exto   :: "('s => 't TorN) => ('s TorN => 't TorN)"
  ext2o   :: "('s => 't TorN set) => ('s TorN => 't TorN set)"
  extos  :: "('s => 't TorN set) => ('s TorN set => 't TorN set)"
  seq      :: "[('s, 't) vacmd, ('t, 'u) vacmd] => ('s, 'u) vacmd"
  terms :: "('s, 't) vacmd => ('s, 't) vacmd"
  ntany     :: "('s, 't) vacmd => ('s, 't) vacmd"
  swap_gc :: "'s set TorN => 's TorN set"

defs
  abort_def : "abort st == {NonTerm}"
  magic_def : "magic st == {}"
  perhaps_def : "perhaps st == {Term st, NonTerm}"
  unitos_def : "unitos st == {Term st}"
  terms_def : "terms A st == A st - {NonTerm}"
  ntany_def : "ntany A st == if NonTerm : A st then UNIV else A st"
  (* extos_def : "extos f crs == Union (ext2o f ` crs)" *)
  (* seq_def : "seq cm1 cm2 state == extos cm2 (cm1 state)" *)

inductive "seq C1 C2 state"
  intros
    INT : "NonTerm : C1 state ==> NonTerm : seq C1 C2 state"
    IT : "[| Term s1 : C1 state; cr2 : C2 s1 |] ==> cr2 : seq C1 C2 state"
  
inductive "extos f crs"
  intros
    extos_NT : "NonTerm : crs ==> NonTerm : extos f crs"
    extos_T : "Term st : crs ==> oc : f st ==> oc : extos f crs"
  
inductive "mapos f crs"
  intros
    mapos_NT : "NonTerm : crs ==> NonTerm : mapos f crs"
    mapos_T : "Term st : crs ==> Term (f st) : mapos f crs"

primrec
  mapo_NT : "mapo f NonTerm = NonTerm"
  mapo_T  : "mapo f (Term st) = Term (f st)"

primrec
  exto_NT  : "exto f NonTerm = NonTerm"
  exto_T  : "exto f (Term st) = f st" 

primrec
  ext2o_NT  : "ext2o f NonTerm = {NonTerm}"
  ext2o_T  : "ext2o f (Term st) = f st"

primrec 
  swap_gc_NT : "swap_gc NonTerm = {NonTerm}"
  swap_gc_T : "swap_gc (Term S) = Term ` S"

(** refinement related stuff, preconditions, postconditions **)

consts
  sts_of_ocs :: "'t TorN set => 't set"
  allfs :: "[('t => bool), ('s => 't TorN set), 's] => bool"
  gencref :: "[('s, 't) vacmd, ('s, 't) vacmd] => bool"
  totcref :: "[('s, 't) vacmd, ('s, 't) vacmd] => bool"
  totceqv :: "[('s, 't) vacmd, ('s, 't) vacmd] => bool"
  partcref :: "[('s, 't) vacmd, ('s, 't) vacmd] => bool"
  slpref :: "[('s, 't) vacmd, ('s, 't) vacmd] => bool"
  egMil :: "[('s, 't) vacmd, ('s, 't) vacmd] => bool"

consts
  (* making types as general as possible, usually 't is 's *)
  trmm    :: "('s, 't) vacmd => 's => bool"
  (* slpm = strongest postcondition of Lermer, Fidge, Hayes, CATS 2003, p67 *)
  wlpm :: "('s, 't) vacmd => ('t => bool) => ('s => bool)"
  wpm :: "('s, 't) vacmd => ('t => bool) => ('s => bool)"
  slpm :: "('s, 't) vacmd => ('s => bool) => ('t => bool)"
  (* strongest postcondition as a set rather than a predicate *)
  slps :: "('s, 't) vacmd => 's set => 't set"
  (* making types as general as possible, usually 'oc is 's TorN *)
  wpom :: "('s => 'oc set) => ('oc => bool) => ('s => bool)"
  spom :: "('s => 'oc set) => ('s => bool) => ('oc => bool)"
  (* conjugate of such a transformer *)
  cnjg :: "('a => ('s => bool) => ('oc => bool)) =>
    ('a => ('s => bool) => ('oc => bool))"

defs
  (* all final states satisfy f *)
  allfs_def : "allfs f C st == Ball (sts_of_ocs (C st)) f" 

inductive "sts_of_ocs ocs" (* set of final states *)
  intros 
    tI : "Term s : ocs ==> s : sts_of_ocs ocs"

defs 
  totcref_def : "totcref A B == (ALL Q. wpm A Q ---> wpm B Q)"
  totceqv_def : "totceqv A B == totcref A B & totcref B A"
  partcref_def : "partcref A B == (ALL Q. wlpm A Q ---> wlpm B Q)"
  slpref_def : "slpref A B == (ALL Q. slpm B Q ---> slpm A Q)"
  gencref_def : "gencref A B == partcref A B & (trmm A ---> trmm B)"
  egMil_def  : "egMil A B == totcref A B & partcref B A"

defs
  trmm_def : "trmm C state == ~ (NonTerm : C state)"
  wlpm_def : "wlpm C P state == ALL nst. Term nst : C state --> P nst"
  wpm_def : "wpm C P == wlpm C P && trmm C"
  slpm_def : "slpm C P state == EX sb. P sb & Term state : C sb"
  slps_def : "slps C bs == Term -` UNION bs C"
  wpom_def : "wpom C occ state == ALL oc: C state. occ oc"
  spom_def : "spom C P oc == EX sb. P sb & oc : C sb"
  cnjg_def : "cnjg pt A pc == Not o pt A (Not o pc)"

consts
  pred_upd  :: "(('n, 'v) state => bool) => 'n => 
    ('n, 'v) expMngTy => (('n, 'v) state => bool)"
  forallp :: "'n => (('n, 'v) state => bool) => ('n, 'v) state => bool"

defs
  pred_upd_def : "pred_upd P v t s == P (s (v := t s))"
  forallp_def : "forallp var pred st == ALL n. pred (st (var := n))" 

end

    
    
