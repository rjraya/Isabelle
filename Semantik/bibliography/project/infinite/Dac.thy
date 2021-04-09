
theory Dac imports Dmng begin 

(* relations between states, eg abstract and concrete states,
  motivated by Dunne, Introducing Backward Refinement into B.  ZB 2003 
  can we start by doing this more simply, ie ignoring termination *)

(*
consts
  liftoc :: "('s * 't) set => ('s TorN * 't TorN) set"
  liftst1 :: "'s acmd => ('s * 't) acmd"
  liftst2 :: "'t acmd => ('s * 't) acmd"
  relmap :: "('a => 'b) => ('a * 'a) set => ('b * 'b) set"

inductive "relmap f r"
  intros
    I : "(a, b) : r ==> (f a, f b) : relmap f r"
    
inductive "liftoc r"
  intros
    INT : "(NonTerm, NonTerm) : liftoc r"
    IT  : "(s, t) : r ==> (Term s, Term t) : liftoc r"
    
primrec
  liftst1_def : "liftst1 A (a, c) = mapos (%b. (b, c)) (A a)"
primrec
  liftst2_def : "liftst2 C (a, c) = mapos (%d. (a, d)) (C c)"
*)

(* stuff used by Dunne, Introducing Backward Refinement into B.  ZB 2003 *)
(*
consts
  arp :: "'a acmd => ('a * 'c => bool) => ('a * 'c => bool)"
  rcp :: "'c acmd => ('a * 'c => bool) => ('a * 'c => bool)"
  fwdref1 :: "'a acmd => 'c acmd => ('a * 'c => bool) => bool"
  fwdref2a :: "'a acmd => 'c acmd => ('a * 'c => bool) => bool"

defs
  arp_def "arp A R ac == Not (wpm (liftst1 A) (Not o R) ac)"
  rcp_def "rcp C == slpm (liftst2 C)"
  fwdref1_def "fwdref1 A C R == trmm A o fst && R ---> trmm C o snd"
  fwdref2a_def "fwdref2a A C R == trmm A o fst && rcp C R ---> arp A R"
*)
types
  'a scmd = "'a => 'a set"

consts
  liftst1 :: "('s => 't set) => ('s * 'u => ('t * 'u) set)"
  liftst2 :: "('s => 't set) => ('u * 's => ('u * 't) set)"

primrec
  liftst1_def : "liftst1 A (a, c) = image (%b. (b, c)) (A a)"
primrec
  liftst2_def : "liftst2 C (a, c) = image (%d. (a, d)) (C c)"

consts
  (* sequencing, ignoring termination *)
  sseq :: "('a => 'b set) => ('b => 'c set) => 'a => 'c set"
  arp :: "('a => 'b set) => ('b * 'c => bool) => ('a * 'c => bool)"
  rap :: "('a => 'b set) => ('a * 'c => bool) => ('b * 'c => bool)"
  rcp :: "('c => 'd set) => ('a * 'c => bool) => ('a * 'd => bool)"
  crp :: "('c => 'd set) => ('a * 'd => bool) => ('a * 'c => bool)"
  fwdrefg :: 
    "['a => 'b set, 'c => 'd set, 'a * 'c => bool, 'b * 'd => bool] => bool" 
  bwdrefg :: 
    "['a => 'b set, 'c => 'd set, 'a * 'c => bool, 'b * 'd => bool] => bool" 
  fwdinit :: "['a => 'b set, 'c => 'd set, 'b * 'd => bool] => bool" 
  bwdinit :: "['a => 'b set, 'c => 'd set, 'b * 'd => bool] => bool" 
  fwdref2a :: "'a scmd => 'c scmd => ('a * 'c => bool) => bool"
  bwdref2a :: "'a scmd => 'c scmd => ('a * 'c => bool) => bool"
  init :: "'a set" (* initial states of any given state type,
    program generating initial states is %s. init *)

defs
  sseq_def : "sseq A B == rel2svf (svf2rel B O svf2rel A)"
  (* that is, svf2rel (A1 ; A2) = svf2rel A2 O svf2rel A1 *)

  (* re forward refinement, arp A R = <A> R, rcp C R = R [C] *)
  arp_def : "arp A == cnjg wpom (liftst1 A)"
  rcp_def : "rcp C == spom (liftst2 C)"
  fwdrefg_def : "fwdrefg A C R S == rcp C R ---> arp A S"
  fwdref2a_def : "fwdref2a A C R == fwdrefg A C R R"

  (* re backward refinement, rap A R = R [A], crp C R = <C> R *)
  rap_def : "rap A == spom (liftst1 A)"
  crp_def : "crp C == cnjg wpom (liftst2 C)"
  bwdrefg_def : "bwdrefg A C R S == crp C S ---> rap A R"
  bwdref2a_def : "bwdref2a A C R == bwdrefg A C R R"
  
  fwdinit_def : "fwdinit AI CI R == fwdrefg AI CI (%p. True) R"
  bwdinit_def : "bwdinit AI CI R == bwdrefg AI CI (%p. True) R"
  (*
  fwdinit_def : "fwdinit AI CI R == rcp CI (%p. True) ---> arp AI R"
  bwdinit_def : "bwdinit AI CI R == crp CI R ---> rap AI (%p. True)"
  *)

 
end 

