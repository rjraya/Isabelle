
theory Dtcv imports Dtcr Dvars begin

consts
  assignv_tc  :: "'n => 'v => ('n, 'v) state tccmd"
  assignvs_tc  :: "'n set => ('n, 'v) state => ('n, 'v) state tccmd"
  assigne_tc  :: "'n => ('n, 'v) expMngTy => ('n, 'v) state tccmd"
  cmd_indep_tc   :: "'n set => ('n, 'v) state tccmd => bool"
  frame_tc   :: "('n, 'v) state tccmd => 'n set => bool"
  prdf_tc :: "'n set => ('n, 'v) state => ('n, 'v) state tccmd =>
    ('n, 'v) state => bool"
  revert_tc  :: "'n set => ('n, 'v) state tccmd => ('n, 'v) state tccmd"
  (*
  indetass:: "'n set => (('n, 'v) state * ('n, 'v) state) set => 
    ('n, 'v) state tccmd"
  at, ata :: "'n set => ('n, 'v) state tccmd => ('n, 'v) state tccmd"
  allvars :: "'n set => ('n, 'v) bexpMngTy => ('n, 'v) bexpMngTy"
*)

(* indeterminate assignment, section 9.1, old and new states satisfy 
  predicate, and only vars listed are changed *)
defs
  (* assignment of value to variable, and expression to variable *)

  assignv_tc_def : "assignv_tc chvar n state == Term {(state (chvar := n))}"

  assigne_tc_def : "assigne_tc chvar E state == assignv_tc chvar (E state) state"

  (* assignvs :: "'n set => ('n, 'v) state => ('n, 'v) state tccmd"
    get new state which is like state except on members of vars,
    where the value is given by primed *)
  
  assignvs_tc_def : "assignvs_tc vars primed state ==
    Term {(setvars vars primed state)}"

  (* frame_tc :: "('n, 'v) state tccmd => 'n set => bool"
    means command A can be regarded as having frame f, 
    ie A does not change vars outside f *)
  frame_tc_def : 
    "frame_tc A f == ALL st nst S v. v ~: f -->
      A st = Term S --> nst : S --> nst v = st v"

  (* for total correctness, Dunne, ZB2002 *)
  prdf_tc_def : "prdf_tc vars s' A == 
    Not o wp_tc A (%s. EX v : vars. s v ~= s' v)"

  (* revert_tc  :: "'n set => ('n, 'v) state tccmd => ('n, 'v) state tccmd"
    modify final states of command by setting members of vars to
    initial values *)
  revert_tc_def : "revert_tc vars A initst == 
    mapo (image (setvars vars initst)) (A initst)"

(*
  indetass_def : "indetass vars P state == 
    Term ` ((P Int chst vars) `` {state})"

  (* at      :: "'n set => ('n, 'v) state tccmd => ('n, 'v) state tccmd" *)
  at_def : "at vars A initst == let 
      initptf = %primed. setvars vars primed initst ;
      initptc = %x. UNION UNIV (A o initptf)
    in revert vars initptc initst"
  
  allvars_def : "allvars vars B state == 
    ALL primed. B (setvars vars primed state)"
  
  (* weaker notion of independence for a command, changing certain 
    variables commutes with running the command *)
  cmd_indep_def : "cmd_indep vars cmd == ALL primed st.
    cmd (setvars vars primed st) = mapos (setvars vars primed) (cmd st)"
  
consts
  pccomb :: "['n set, 'n set] => ('n, 'v) state =>
    (('n, 'v) state * ('n, 'v) state) => ('n, 'v) state TorN set"
  pcompfr :: "['n set, ('n, 'v) state tccmd] => 
    ['n set, ('n, 'v) state tccmd] => ('n, 'v) state tccmd"

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
    
*)
end

