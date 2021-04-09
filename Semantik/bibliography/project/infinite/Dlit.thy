

theory Dlit imports Drc Dvars begin 

types
  cmdMeaning = "(string, nat) cmdMngTy"
  bexpMeaning = "(string, nat) bexpMngTy"
  expMeaning = "(string, nat) expMngTy"

datatype ('n, 'v) exp = Val 'v
	     | Op "'v list => 'v" "('n, 'v) exp list"
             | Var 'n

datatype ('n, 'v) bexp = Rel "'v list => bool" "('n, 'v) exp list"
                       | BRel "bool list => bool" "('n, 'v) bexp list"

datatype ('n, 'v) command = Skip
   | Seq "('n, 'v) command" "('n, 'v) command" ("_ ;; _" [60,61] 60)
   | Ass "'n" "(('n, 'v) exp)" ("_ ::= _" [90, 70] 70)
   | ITE "(('n, 'v) bexp)" "('n, 'v) command" "('n, 'v) command" 
       ("if _ then _ else _ end" [0, 0, 0] 70)
   | IT "(('n, 'v) bexp)" "('n, 'v) command" ("if _ then _ end" [0, 0] 70)
   | While "(('n, 'v) bexp)" "('n, 'v) command" ("while _ do _ end" [0, 0] 70)
   | Guard "(('n, 'v) bexp)" "('n, 'v) command" ("_ -> _" [80, 70] 70)
   | Precon "(('n, 'v) bexp)" "('n, 'v) command" 
   | Pcomp "('n, 'v) command" "('n, 'v) command" ("_ || _" [60, 61] 60)
   | BC "('n, 'v) command" "('n, 'v) command" 
   | Concert "('n, 'v) command" "('n, 'v) command" ("_ ## _" [62, 63] 62)
   | Rep nat "('n, 'v) command"
   | RepClos "('n, 'v) command"
   | indetAss "('n list)" "(('n, 'v) bexp)"

consts
  expMng   :: "('n, 'v) exp => ('n, 'v) state => 'v"
  expsMng   :: "('n, 'v) exp list => ('n, 'v) state => 'v list"
  bexpMng   :: "('n, 'v) bexp => ('n, 'v) state => bool"
  bexpsMng   :: "('n, 'v) bexp list => ('n, 'v) state => bool list"
  expSub   :: "'n => ('n, 'v) exp => ('n, 'v) exp => ('n, 'v) exp"
  expsSub   :: "'n => ('n, 'v) exp => ('n, 'v) exp list => ('n, 'v) exp list"
  bexpSub  :: "'n => ('n, 'v) exp => ('n, 'v) bexp => ('n, 'v) bexp"
  bexpsSub  :: "'n => ('n, 'v) exp => ('n, 'v) bexp list => ('n, 'v) bexp list"
  cmdMng   :: "('n, 'v) command => ('n, 'v) cmdMngTy"

primrec
  "expMng (Val num) state = num"
  "expMng (Op f exps) state = f (expsMng exps state)"
  "expMng (Var var) state = state var"

  "expsMng [] state = []"
  "expsMng (e # es) state = expMng e state # expsMng es state"

primrec
  "expSub var rexp (Val num) = Val num"
  "expSub var rexp (Op f exps) = Op f (expsSub var rexp exps)"
  "expSub var rexp (Var var') = (if var = var' then rexp else Var var')"

  "expsSub var rexp [] = []"
  "expsSub var rexp (e # es) = expSub var rexp e # expsSub var rexp es"

primrec
  "bexpMng (Rel f exps) state = f (expsMng exps state)"
  "bexpMng (BRel f bexps) state = f (bexpsMng bexps state)"

  "bexpsMng [] state = []"
  "bexpsMng (e # es) state = bexpMng e state # bexpsMng es state"

primrec
  "bexpSub var rexp (Rel f exps) = Rel f (expsSub var rexp exps)"
  "bexpSub var rexp (BRel f bexps) = BRel f (bexpsSub var rexp bexps)"

  "bexpsSub var rexp [] = []"
  "bexpsSub var rexp (e # es) = bexpSub var rexp e # bexpsSub var rexp es"

primrec
  "cmdMng Skip state = {Term state}"
  "cmdMng (Seq cmd1 cmd2) state = seq (cmdMng cmd1) (cmdMng cmd2) state " 
  "cmdMng (Guard bexp cmd) state = guard (bexpMng bexp) (cmdMng cmd) state"
  "cmdMng (Precon bexp cmd) state = precon (bexpMng bexp) (cmdMng cmd) state"
  "cmdMng (BC cmd1 cmd2) state = choice {cmdMng cmd1, cmdMng cmd2} state" 
  "cmdMng (cmd1 ## cmd2) state = conc (cmdMng cmd1) (cmdMng cmd2) state" 
  "cmdMng (While bexp cmd) state = 
    wreach (guard (bexpMng bexp) (cmdMng cmd)) state Int
      ({NonTerm} Un (Term ` Collect (Not o bexpMng bexp))) Un
      (if infch (guard (bexpMng bexp) (cmdMng cmd)) state then {NonTerm}
	else {})"
  "cmdMng (Ass var exp) state = {Term (state (var := expMng exp state))}"
  "cmdMng (ITE bexp tcmd ecmd) state = 
    (if bexpMng bexp state then cmdMng tcmd state 
    else cmdMng ecmd state)"
  "cmdMng (IT bexp tcmd) state = 
    (if bexpMng bexp state then cmdMng tcmd state else {Term state})"
  "cmdMng (Rep n cmd) state = rep n (cmdMng cmd) state"
  cmdMng_RepClos : "cmdMng (RepClos cmd) state = repstar (cmdMng cmd) state"

end
  
