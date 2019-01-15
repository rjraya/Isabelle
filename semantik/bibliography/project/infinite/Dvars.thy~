
theory Dvars imports Dmc begin  

consts
  assignv  :: "'n => 'v => ('n, 'v) state acmd"
  assignvs  :: "'n set => ('n, 'v) state => ('n, 'v) state acmd"
  assigne  :: "'n => ('n, 'v) expMngTy => ('n, 'v) state acmd"
  chst    :: "'n set => (('n, 'v) state * ('n, 'v) state) set"
  frame   :: "('n, 'v) state acmd => 'n set => bool"
  indetass:: "'n set => (('n, 'v) state * ('n, 'v) state) set => 
    ('n, 'v) state acmd"
  setvars :: "'n set => ('n, 'v) state => ('n, 'v) state => ('n, 'v) state"
  revert  :: "'n set => ('n, 'v) state acmd => ('n, 'v) state acmd"
  at :: "'n set => ('n, 'v) state acmd => ('n, 'v) state acmd"
  ata :: "'n set => ('n, 'v) state acmd => ('n, 'v) state acmd"
  allvars :: "'n set => ('n, 'v) bexpMngTy => ('n, 'v) bexpMngTy"
  indep   :: "'n set => (('n, 'v) state => 'a) => bool"
  cmd_indep   :: "'n set => ('n, 'v) state acmd => bool"
  prds :: "'n set => ('n, 'v) state => ('n, 'v) state acmd =>
    ('n, 'v) state => bool"
  prdts :: "'n set => ('n, 'v) state => ('n, 'v) state acmd =>
    ('n, 'v) state => bool"

(* indeterminate assignment, section 9.1, old and new states satisfy 
  predicate, and only vars listed are changed *)
defs
  (* assignment of value to variable, and expression to variable *)

  assignv_def : "assignv chvar n state == {Term (state (chvar := n))}"

  assigne_def : "assigne chvar E state == assignv chvar (E state) state"

  (* chst    :: "'n set => (('n, 'v) state * ('n, 'v) state) set"
    relation on states, holds when they differ only on vars only *)
  chst_def : "chst vars ==
    {(state, nst). ALL str. nst str ~= state str --> str : vars}"

  (* frame :: "('n, 'v) state acmd => 'n set => bool"
    means command A can be regarded as having frame f, 
    ie A does not change vars outside f *)
  frame_def : 
    "frame A f == ALL st nst v. v ~: f --> Term nst : A st --> nst v = st v"

  indetass_def : "indetass vars P state == 
    Term ` ((P Int chst vars) `` {state})"

  prds_def : "prds vars primed A == 
    Not o wlpm A (%st. EX str : vars. st str ~= primed str)"

  (* corresponding notion for total correctness, Dunne, ZB2002 *)
  prdts_def : "prdts vars primed A == 
    Not o wpm A (%st. EX str : vars. st str ~= primed str)"

  (* setvars :: "'n set => ('n, 'v) state => ('n, 'v) state => ('n, 'v) state"
    assignvs :: "'n set => ('n, 'v) state => ('n, 'v) state acmd"
    get new state which is like state except on members of vars,
    where the value is given by primed *)
  setvars_def : "setvars vars primed state str == 
    if str : vars then primed str else state str"
  
  assignvs_def : "assignvs vars primed state ==
    {Term (setvars vars primed state)}"

  (* revert  :: "'n set => ('n, 'v) state acmd => ('n, 'v) state acmd"
    modify final states of command by setting members of vars to
    initial values *)
  revert_def : "revert vars A initst == 
    mapos (setvars vars initst) (A initst)"

  (* at      :: "'n set => ('n, 'v) state acmd => ('n, 'v) state acmd" *)
  at_def : "at vars A initst == let 
      initptf = %primed. setvars vars primed initst ;
      initptc = %x. UNION UNIV (A o initptf)
    in revert vars initptc initst"
  
  allvars_def : "allvars vars B state == 
    ALL primed. B (setvars vars primed state)"
  
  indep_def : "indep vars fun == 
    ALL (state, statech) : chst vars. fun state = fun statech"

  (* weaker notion of independence for a command, changing certain 
    variables commutes with running the command *)
  cmd_indep_def : "cmd_indep vars cmd == ALL primed st.
    cmd (setvars vars primed st) = mapos (setvars vars primed) (cmd st)"
  
consts
  pccomb :: "['n set, 'n set] => ('n, 'v) state =>
    (('n, 'v) state * ('n, 'v) state) => ('n, 'v) state TorN set"
  pcompfr :: "['n set, ('n, 'v) state acmd] => 
    ['n set, ('n, 'v) state acmd] => ('n, 'v) state acmd"

primrec
  pccomb_def : "pccomb frA frB initst (stA, stB) = 
    (let compat = (ALL str: frA Int frB. stA str = stB str) ;
      combst = (%str. if str : frA then stA str 
        else if str : frB then stB str
	else initst str)
    in if compat then {Term combst} else {})"

defs
  pcompfr_def : "pcompfr frA A frB B state == 
    let tsA = {st. Term st : A state} ;
      tsB = {st. Term st : B state} ;
      nont = {NonTerm} Int (A state Un B state)
    in nont Un UNION (tsA <*> tsB) (pccomb frA frB state)"
    
(** example from section 9.2 (unbounded nondeterminism) **)

end

