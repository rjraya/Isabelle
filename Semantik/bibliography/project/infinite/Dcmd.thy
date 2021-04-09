

theory Dcmd imports Dlit begin 

consts
  lookup   :: "'n => ('n, 'v) state => 'v"
  trm'	   :: "('n, 'v) command => ('n, 'v) bexpMngTy"
  trm 	   :: "('n, 'v) command => ('n, 'v) bexp"
  (* note - wlp second argument must be bexp, not bexpMngTy,
    because must be able to substitute in it (rule for wlp for Ass) ;
    therefore wlp result must also be bexp (rule for wlp for Seq) *)
  wlp  :: "('n, 'v) command => ('n, 'v) bexp => ('n, 'v) bexp"
  wp  :: "('n, 'v) command => ('n, 'v) bexp => ('n, 'v) bexp"
  wlpRep  :: "nat => ('n, 'v) command => ('n, 'v) bexp => ('n, 'v) bexp"
  wlp' :: "('n, 'v) command => ('n, 'v) bexp => ('n, 'v) bexpMngTy"
  wp':: "('n, 'v) command => ('n, 'v) bexp => ('n, 'v) bexpMngTy"
  frame    :: "('n, 'v) command => 'n set"
  Abort    :: "('n, 'v) command"
  Perhaps  :: "('n, 'v) command"
  Magic    :: "('n, 'v) command"
  EgMil    :: "('n, 'v) command => ('n, 'v) command => bool"

defs
  trm'_def : "trm' cmd == trmm (cmdMng cmd)"
  wlp'_def : "wlp' cmd bexp == wlpm (cmdMng cmd) (bexpMng bexp)"
  wp'_def : "wp' cmd bexp == wpm (cmdMng cmd) (bexpMng bexp)"

primrec
  "frame Skip = {}"
  "frame (Seq cmd1 cmd2) = (frame cmd1) Un (frame cmd2)" 
  "frame (Guard bexp cmd) = frame cmd"
  "frame (Precon bexp cmd) = frame cmd"
  "frame (BC cmd1 cmd2) = (frame cmd1) Un (frame cmd2) " 
  "frame (While bexp cmd) = frame cmd"
  "frame (Ass var exp) = {var}"
  "frame (ITE bexp tcmd ecmd) = (frame tcmd) Un (frame ecmd) " 
  "frame (IT bexp tcmd) = frame tcmd"

consts
  andf :: "bool list => bool"
  orf :: "bool list => bool"
  impf :: "bool list => bool"
  notf :: "bool list => bool"
  itef :: "bool list => bool"

primrec 
  orf_Cons : "orf (b # bs) = (b | orf bs)"
  orf_Nil : "orf [] = False"

primrec 
  impf_Cons : "impf (b # bs) = (Not b | orf bs)"

primrec 
  notf_Cons : "notf (b # bs) = Not b"

primrec 
  andf_Cons : "andf (b # bs) = (b & andf bs)"
  andf_Nil : "andf [] = True"

recdef itef "{}"
  "itef [c,t,e] = (if c then t else e)"

consts
  T :: "('n, 'v) bexp" 
  F :: "('n, 'v) bexp" 

defs
  T_def : "T == BRel (%l. True) []"
  F_def : "F == BRel (%l. False) []"
 
primrec
  "wlp Skip R = R"
  "wlp (Seq C1 C2) R = wlp C1 (wlp C2 R)"
  "wlp (Guard bexp C) R = BRel impf [bexp, (wlp C R)]"
  "wlp (Precon bexp C) R = wlp C R"
  "wlp (BC C1 C2) R = BRel andf [wlp C1 R, wlp C2 R]" 
  "wlp (Concert C1 C2) R = BRel andf [wlp C1 R, wlp C2 R]" 
  "wlp (Ass var exp) R = bexpSub var exp R"
  "wlp (ITE bexp tcmd ecmd) R = BRel itef [bexp, (wlp tcmd R), (wlp ecmd R)]" 
  "wlp (IT bexp tcmd) R = BRel itef [bexp, (wlp tcmd R), R]"
  "wlp (Rep n C) R = wlpRep n C R"
  (*
  "wlp (While bexp C) R = wlp C"
*)

defs 
  Magic_def : "Magic == Guard F Skip" (* Magic called Never in first paper *)
  Abort_def : "Abort == Precon F Magic" 
  Perhaps_def : "Perhaps == Precon F Skip"
  EgMil_def : "EgMil A B == 
    totcref (cmdMng A) (cmdMng B) & partcref (cmdMng B) (cmdMng A)"

end

    
(* alternatively, could define wlp A Q (as a bexp) for each command operator,
  and then prove that bexpMng (wlp A Q) = wlp' A Q, similarly for trm *)
    
