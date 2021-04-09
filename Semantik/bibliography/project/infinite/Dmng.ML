
structure Dmng = struct val thy = theory "Dmng" ;
  val ipt_mk_cases = InductivePackage.the_mk_cases thy ; end ;
val _ = use_legacy_bindings Dmng.thy ;

fun uta() = update_thy "Dall" ;
fun utoa() = update_thy_only "Dall" ;
fun ua() = use "Dall.ML" ;

fun utm() = update_thy "Dmng" ;
fun utom() = update_thy_only "Dmng" ;
fun um() = use "Dmng.ML" ;

(* Addsimps [unitos_def] ; causes weird substitutions - TO CHECK *)
Addsimps [dlidef, liftimp, liftand, liftor] ;

AddSIs [rel2svf.I, svf2rel.I, revsvf.I] ;
val rel2svfE = mkpE rel2svf.elims ;
val svf2rel_mk_cases = Dmng.ipt_mk_cases "Dmng.svf2rel" ;
val revsvf_mk_cases = Dmng.ipt_mk_cases "Dmng.revsvf" ;
val mapos_mk_cases = Dmng.ipt_mk_cases "Dmng.mapos" ;
val svf2relE = svf2rel_mk_cases "(a, b) : svf2rel f" ;
val revsvfE = revsvf_mk_cases "s : revsvf f t" ;
AddSEs [revsvfE, rel2svfE, svf2relE] ;

val _ = bind_thm ("spomI", conjI RS (exI RS (spom_def RS defD2))) ; 
val _ = bind_thm ("spomE", tacthm (etac conjE 2) (spom_def RS defD1 RS exE)) ; 

val sts_of_ocsE = mkpE sts_of_ocs.elims ;
val sts_of_ocsD = tacthm (atac 2) sts_of_ocsE ;
val sts_of_ocs_emptyE = sts_of_ocsD RS emptyE ;
AddSEs [sts_of_ocs_emptyE] ;
AddSIs [sts_of_ocs.intros] ;
AddSEs [sts_of_ocsE] ;

val _ = qed_goal "sts_of_ocs_ins_NT" Dmng.thy
  "sts_of_ocs (insert NonTerm S) = sts_of_ocs S" fn_ft1 ;

val _ = qed_goal "sts_of_ocs_ins_Term" Dmng.thy
  "sts_of_ocs (insert (Term s) S) = insert s (sts_of_ocs S)" fn_ft1 ;
Addsimps [sts_of_ocs_ins_NT, sts_of_ocs_ins_Term] ;

val _ = qed_goal "svf_rel_bij" Dmng.thy 
  "svf2rel (rel2svf r) = r & rel2svf (svf2rel f) = f"
  (fn _ => [ (safe_tac (cis [ext]))]) ;

Addsimps [svf_rel_bij] ;

val _ = qed_goalw "spom_rel" Dmng.thy [spom_def]
  "spom C P oc = (oc : svf2rel C `` Collect P)"
  (fn _ => [ Safe_tac, (rtac ImageI 1), Auto_tac]) ;

val _ = qed_goalw "wpom_rel" Dmng.thy [wpom_def]
  "wpom C Q st = (svf2rel C `` {st} <= Collect Q)"
  (fn _ => [ Safe_tac, (dtac subsetD 2), (rtac ImageI 2), Auto_tac]) ;

val _ = qed_goal "revsfv_converse" Dmng.thy 
  "revsvf f = rel2svf (converse (svf2rel f))"
  (fn _ => [ (safe_tac (cis [ext]))]) ;

val _ = qed_goal "wpo_spo_conj" Dmng.thy
  "wpom C P = Not o spom (revsvf C) (Not o P)"
  (fn _ => [ (safe_tac (cis [ext])),
    (auto_tac (cesimps [wpom_def, spom_def])) ]) ;

val _ = qed_goal "exto_Term" Dmng.thy "exto Term = id" 
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), Auto_tac ]) ;

Addsimps [exto_Term] ;

val _ = qed_goalw "map_defo" Dmng.thy [meta_eq_def] "mapo f == exto (Term o f)"
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), Auto_tac ]) ;

val _ = qed_goal "exto_fun" Dmng.thy 
  "exto (exto g o f) = exto g o exto f"
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), Auto_tac ]) ;

val _ = qed_goal "extomapo" Dmng.thy
  "exto g o mapo f = exto (g o f)"
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), (ALLGOALS Asm_simp_tac)]) ;

val _ = qed_goal "mapo_o" Dmng.thy
  "mapo g o mapo f = mapo (g o f)"
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), (ALLGOALS Asm_simp_tac)]) ;

val _ = qed_goalw_spec_mp "extos_def" Dmng.thy [meta_eq_def]
  "extos f crs == Union (ext2o f ` crs)"
  (fn _ => [ Safe_tac, (case_tac "xa" 2),
    (ALLGOALS (force_tac (ces (extos.elims :: extos.intros), simpset ()))) ]) ;

val _ = qed_goal "Term_natural" Dmng.thy 
  "mapo f o Term = Term o f" (fn _ => [ (rtac ext 1), Auto_tac ]) ;

val _ = qed_goal "exto_runit" Dmng.thy 
  "exto f o Term = f" (fn _ => [ (rtac ext 1), Auto_tac ]) ;
Addsimps [exto_runit] ;

val seqE = tacthm (rotate_tac 1 3) (mkpE seq.elims) ;
val seqINT = seq.INT ;
val seqIT = seq.IT ;

val _ = qed_goalw_spec_mp "seq_def" Dmng.thy [meta_eq_def, extos_def]
  "seq cm1 cm2 state == extos cm2 (cm1 state)"
  (fn _ => [ (Safe_tac),
    (case_tac "xa" 2), (etac seqE 1),
    (ALLGOALS (force_tac (ces seq.intros, simpset ()))) ]) ; 

(* following use seq_def as definition 
val _ = qed_goal_spec_mp "seqINT" Dmng.thy 
  "NonTerm : C1 state --> NonTerm : seq C1 C2 state" 
  (fn _ => [EVERY (ft_mng []), Force_tac 1]) ;

val () = qed_goal_spec_mp "seqIT" Dmng.thy 
  "Term s1 : C1 state --> cr2 : C2 s1 --> cr2 : seq C1 C2 state" 
  (fn _ => [EVERY (ft_mng []), Force_tac 1]) ;

val _ = qed_goal "seqE" Dmng.thy
  "[| cr : seq C1 C2 state ; \
    \ [| cr = NonTerm ; NonTerm : C1 state |] ==> P ; \
    \ !! s1. [| cr : C2 s1 ; Term s1 : C1 state |] ==> P |] ==> P"
  (fn [p1, p2, p3] => [(cut_facts_tac [p1] 1), 
    (EVERY (ft_mng [])), (case_tac "x" 1), 
    (Asm_full_simp_tac 1), (eatac p2 1 1), 
    (Asm_full_simp_tac 1), (eatac p3 1 1)]) ; 
*)

val defs_mng = [ wpm_def, wlpm_def, slpm_def, slps_def, trmm_def,
  terms_def, ntany_def, abort_def, magic_def, perhaps_def,
  seq_def, extos_def, unitos_def] ;

val cs_mng = cesimps defs_mng ;

fun ft_ss defs = EVERY
  [REPEAT (resolve_tac [ext, impI] 1), auto_tac (cesimps defs)] ;
fun ft_mng _ = [REPEAT (resolve_tac [set_ext, ext, impI] 1), auto_tac cs_mng] ;

val _ = qed_goal "Term_image" Dmng.thy 
  "(Term st : Term ` sts) = (st : sts)" fn_at ;
Addsimps [Term_image] ;

(** useful lemmas *)

val _ = bind_thm ("liftimp_refl", (prove_goal Dmng.thy
  "(P ---> P)" (fn _ => [Auto_tac]))) ;
AddIffs [liftimp_refl] ;

val _ = bind_thm ("liftimp_trans", meta_std (prove_goal Dmng.thy
  "(P ---> Q) & (Q ---> R) --> (P ---> R)" (fn _ => [Auto_tac]))) ;

val _ = bind_thm ("lift_eqE", prove_goal Dmng.thy
  "[| P = Q ; [| (P ---> Q) ; (Q ---> P) |] ==> R |] ==> R"
  (fn [peq, p2] => [rtac p2 1, (ALLGOALS (simp_tac (esimps [peq])))])) ;

val _ = bind_thm ("lift_eqI", meta_std (prove_goal Dmng.thy
  "(P ---> Q) & (Q ---> P) --> (P = Q)" 
  (fn _ => [rtac impI 1, rtac ext 1, 
    (* Auto_tac and Force_tac loop here *)
    Full_simp_tac 1, Fast_tac 1]))) ;

val _ = qed_goal "liftandD1" Dmng.thy "P && Q ---> P" (fn _ => [Auto_tac]) ;
val _ = qed_goal "liftandD2" Dmng.thy "P && Q ---> Q" (fn _ => [Auto_tac]) ;

val _ = qed_goal "wp_conj" Dmng.thy
  "wpm C (Q && R) = (wpm C Q && wpm C R)" ft_mng ;

(* generalised conjunctivity, only for non-empty conjunctions *)
val _ = qed_goal_spec_mp "wp_gen_conj" Dmng.thy
  "Q : Qs --> wpm C (%s. ALL Q : Qs. Q s) s = (ALL Q : Qs. wpm C Q s)" ft_mng ;

val _ = qed_goal "wlp_conj" Dmng.thy
  "wlpm C (Q && R) = (wlpm C Q && wlpm C R)" ft_mng ;

(* generalised conjunctivity, does not require non-empty conjunctions *)
val _ = qed_goal_spec_mp "wlp_gen_conj" Dmng.thy
  "wlpm C (%s. ALL Q : Qs. Q s) s = (ALL Q : Qs. wlpm C Q s)" ft_mng ;

val _ = qed_goal "wp_trm" Dmng.thy "trmm C = wpm C (%st. True)" ft_mng ;
val _ = qed_goal "wpm_term" Dmng.thy "wpm (terms A) = wlpm A" ft_mng ; 
val _ = qed_goal "wlpm_term" Dmng.thy "wlpm (terms A) = wlpm A" ft_mng ; 
val _ = qed_goal "trm_term" Dmng.thy "trmm (terms A) s" ft_mng ; 
val _ = qed_goal "term_term" Dmng.thy "terms (terms A) = terms A" ft_mng ; 
val _ = qed_goal "ntany_ntany" Dmng.thy "ntany (ntany A) = ntany A" ft_mng ; 

val _ = qed_goal "mapos_def" Dmng.thy "mapos f = extos (unitos o f)"
  (fn _ => [ (EVERY (ft_mng [])), (case_tac "xb" 2),
    ((etac mapos.elims THEN_ALL_NEW etac rev_bexI) 1),
    (ALLGOALS (asm_full_simp_tac (esimps [unitos_def]))),
    (ALLGOALS (eresolve_tac mapos.intros)) ]) ;

val _ = qed_goal "mapos_def'" Dmng.thy "mapos f crs = mapo f ` crs"
  (fn _ => [ (rtac set_ext 1), Safe_tac, 
    (case_tac "xa" 2), (etac mapos.elims 1),
    (ALLGOALS Asm_full_simp_tac),
    (TRYALL (eresolve_tac mapos.intros)),
    (ALLGOALS Force_tac) ]) ;

val () = qed_goal "mapT" Dmng.thy 
  "(Term x : mapos f ys) = (EX st. x = f st & Term st : ys)" 
  (fn _ => [ (simp_tac (esimps [mapos.defs]) 1)]) ;

val _ = qed_goal "mapNT" Dmng.thy 
  "(NonTerm : mapos f crs) = (NonTerm : crs)"
  (fn _ => [ (simp_tac (esimps [mapos.defs]) 1)]) ;

val mapos_elimNT = mapos_mk_cases "NonTerm : mapos f S" ;
val mapos_elimT = mapos_mk_cases "Term x : mapos f S" ;

val _ = qed_goal "ext2o_unit" Dmng.thy "ext2o unitos cr = {cr}"
  (fn _ => [(case_tac "cr" 1), auto_tac (cs_mng)]) ;

(** some standard monadic results **)

val _ = qed_goal "left_unit" Dmng.thy "extos f o unitos = f" ft_mng ;
val left_unit' = store_thm ("left_unit'",
  rewrite_rule [o_def] (left_unit RS fun_cong)) ;

val _ = qed_goalw "right_unit" Dmng.thy [extos_def] 
  "extos unitos m = m" (fn _ => [auto_tac (cesimps [ext2o_unit])]) ;

val thss = equalityD1 RSN (2, rev_subsetD) ;

val mtacs = [ (auto_tac (ces [mapos.elims] addSIs mapos.intros, simpset ())), 
  (dresolve_tac mapos.intros 1),
  (etac thss 1), (cong_tac 1), (rtac ext 1), Simp_tac 1] ;

val _ = qed_goal "mapos_id" Dmng.thy "mapos id = id"
  (fn _ => ( [(rtac ext 1), Safe_tac, (case_tac "xa" 2)] @ mtacs)) ;

val _ = qed_goal "mapos_comp" Dmng.thy "mapos g (mapos f x) = mapos (g o f) x"
  (fn _ => mtacs) ;

val rev_bexI = rotate_prems 1 bexI ;

val _ = qed_goal "crs_assoc" Dmng.thy
  "extos h o extos g = extos (extos h o g)"
  (fn _ => [ EVERY (ft_mng []), 
    etac rev_bexI 2, (case_tac "xb" 2), 
    etac rev_bexI 1, (case_tac "xb" 1), 
    (ALLGOALS (force_tac (cesimps defs_mng)))]) ;

val _ = qed_goalw "seq_def'" Dmng.thy [meta_eq_def]
  "seq C1 C2 == extos C2 o C1" 
  (fn _ => [rtac ext 1, (simp_tac (esimps [seq_def]) 1)]) ;

val _ = qed_goalw "seq_assoc" Dmng.thy [seq_def']
  "seq C1 (seq C2 C3) = seq (seq C1 C2) C3"
  (fn _ => [ simp_tac (esimps [crs_assoc RS sym, o_assoc]) 1]) ;

val _ = qed_goal "seq_unitoL" Dmng.thy "seq (unitos o f) A = A o f" ft_mng ; 
val _ = qed_goal "seq_unitL" Dmng.thy "seq unitos A = A" ft_mng ; 
val _ = qed_goal "seq_unitR" Dmng.thy "seq A unitos = A" 
  (fn _ => [rtac ext 1, 
    let val ss = esimps (ext2o_unit :: defs_mng) ;
    in (auto_tac (claset (), ss)) end]) ;

val _ = qed_goal_spec_mp "seq_mono1" Dmng.thy 
  "C state <= C' state --> seq C C2 state <= seq C' C2 state" ft_mng ;
  
val _ = qed_goalw_spec_mp "seq_mono2" Dmng.thy defs_mng
  "(ALL st. C st <= C' st) --> seq C1 C state <= seq C1 C' state"
  (fn _ => [rtac impI 1, rtac Union_least 1, 
    rewtac (mk_eq image_iff), etac bexE 1, 
    rtac subset_trans 1, rtac Union_upper 2, etac imageI 2,
    (case_tac "x" 1), Auto_tac]) ;

(* swap_gc is the swap function for the general correctness monad,
  show it satisfies the swap axioms *)
val _ = qed_goal "S1_gc" Dmng.thy
  "swap_gc o (mapo (image f)) = image (mapo f) o swap_gc"
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), Auto_tac, 
    (rtac image_eqI 1), (etac imageI 2), Simp_tac 1 ]) ;
    
(* S2 is just swap_gc_T *) 

val _ = qed_goal "S3_gc" Dmng.thy "swap_gc (mapo (%x. {x}) oc) = {oc}"
  (fn _ => [ (case_tac "oc" 1), Auto_tac ]) ;
  
val _ = qed_goal "S4_gc" Dmng.thy 
  "ext2o (Union o image swap_gc) = (Union o image swap_gc) o ext2o id"
  (fn _ => [ (rtac ext 1), (case_tac "x" 1), Auto_tac ]) ;


val _ = qed_goal "slpm_fun" Dmng.thy 
  "slpm (unitos o f) Q nst = (nst : f ` Collect Q)" ft_mng ;
val _ = qed_goal "slps_fun" Dmng.thy 
  "slps (unitos o f) Qs = (f ` Qs)" ft_mng ;
val _ = qed_goal "wlpm_fun" Dmng.thy "wlpm (unitos o f) Q = Q o f" ft_mng ;
val _ = qed_goal "wpm_fun" Dmng.thy "wpm (unitos o f) Q = Q o f" ft_mng ;
val _ = qed_goal "trmm_fun" Dmng.thy "trmm (unitos o f) = (%st. True)" ft_mng ;

val _ = qed_goal "slpm_unit" Dmng.thy "slpm unitos Q = Q" ft_mng ;
val _ = qed_goal "wlpm_unit" Dmng.thy "wlpm unitos Q = Q" ft_mng ;
val _ = qed_goal "wpm_unit" Dmng.thy "wpm unitos Q = Q" ft_mng ;
val _ = qed_goal "trmm_unit" Dmng.thy "trmm unitos = (%st. True)" ft_mng ;

val _ = qed_goal "wlpm_conj" Dmng.thy 
  "wlpm A (Q && R) = (wlpm A Q && wlpm A R)"
  (fn _ => [rtac ext 1, rewrite_goals_tac [wlpm_def, liftand], Fast_tac 1]) ;

val _ = qed_goal "wpm_conj" Dmng.thy 
  "wpm A (Q && R) = (wpm A Q && wpm A R)"
  (fn _ => [rtac ext 1, 
    rewrite_goals_tac [liftand, wpm_def, trmm_def, wlpm_def], Fast_tac 1]) ;

val _ = qed_goal "slps_Un" Dmng.thy 
  "slps A (Union Qss) = UNION Qss (slps A)" ft_mng ;

val _ = qed_goal "slps_Un1" Dmng.thy 
  "slps A Q = (UN q: Q. slps A {q})" ft_mng ;

val _ = qed_goal_spec_mp "unique" Dmng.thy
  "trmm A = trmm B --> wlpm A = wlpm B --> A = B"
  (fn _ => [Safe_tac, rtac ext 1, Safe_tac,
    (ALLGOALS (case_tac "xa" THEN'
      (fn i => dres_inst_tac [("x", "%st. st ~= s")] fun_cong (i+1)))), 
    (ALLGOALS (REPEAT o (dres_inst_tac [("x", "x")] fun_cong))), 
    (auto_tac (cesimps [wlpm_def, trmm_def]))]) ; 

val _ = bind_thm ("wlpm_mono_cond", prove_goalw Dmng.thy [wlpm_def, liftimp]
  "(P ---> Q) --> (wlpm A P ---> wlpm A Q)" 
  (fn _ => [Auto_tac]) RS mp) ;
    
val _ = bind_thm ("wpm_mono_cond", prove_goalw Dmng.thy [wpm_def]
  "(P ---> Q) --> (wpm A P ---> wpm A Q)" 
  (fn _ => [ rtac impI 1, (dtac wlpm_mono_cond 1),
    rewrite_goals_tac [liftand, liftimp], Fast_tac 1]) RS mp) ;
    
(* proved again, from conjunctivity, as called for by Dunne's GS paper *)
val _ = bind_thm ("wpm_mono_cond_alt", prove_goalw Dmng.thy []
  "(P ---> Q) --> (wpm A P ---> wpm A Q)" 
  (fn _ => [ (rtac impI 1), 
    (subgoal_tac "(P && Q) = P" 1), (rtac ext 2), Force_tac 2,
    (subgoal_tac "wpm A P = wpm A (P && Q)" 1), Asm_simp_tac 2,
    (etac thin_rl 1), (etac thin_rl 1), (asm_simp_tac HOL_ss 1),
    (rewtac (mk_eq wpm_conj)), (rtac liftandD2 1) ]) RS mp) ;

fun mksli th = rotate_prems 1 (simplify (esimps []) th RS spec RS mp) ;
val [wlpm_mono_cond', wpm_mono_cond', wpm_mono_cond_alt'] = 
  map mksli [wlpm_mono_cond, wpm_mono_cond, wpm_mono_cond_alt] ; 

val _ = qed_goalw "wp_imp_trm" Dmng.thy [liftimp, mk_eq wp_trm] 
  "wpm S Q ---> trmm S"
  (fn _ => [ (Safe_tac), (etac wpm_mono_cond_alt' 1), Simp_tac 1 ]) ;

val wp_imp_trm' = mksli wp_imp_trm ;

(* weak disjunctivity proved from this, as called for by Dunne's GS paper *)
val _ = qed_goalw "wpm_weak_disj" Dmng.thy [liftimp, liftor]
  "wpm S Q V wpm S R ---> wpm S (Q V R)"
  (fn _ => [ Safe_tac, (TRYALL (etac wpm_mono_cond_alt')),
    (TRYALL (rtac ext)), Auto_tac ]) ;

val _ = qed_goalw_spec_mp "wlpm_mono_prog" Dmng.thy [wlpm_def]
  "A state <= B state --> \
    \ (wlpm B Q state --> wlpm A Q state)" (fn _ => [Auto_tac]) ;

val _ = bind_thm ("trmm_mono", prove_goalw Dmng.thy [trmm_def]
  "A state <= B state --> \
    \ (trmm B state --> trmm A state)" (fn _ => [Auto_tac]) RS mp) ;
    
Addsimps [left_unit, left_unit', right_unit, ext2o_unit,
  seq_unitL, seq_unitR, wlpm_unit, wpm_unit, trmm_unit,
  term_term, ntany_ntany] ;

(** section 2 - refinement **)

val _ = qed_goalw "partcref_alt" Dmng.thy 
  [meta_eq_def, liftimp, partcref_def, wlpm_def]
  "partcref A B == (ALL state. B state <= insert NonTerm (A state))" 
  (fn _ => [Auto_tac, 
    (case_tac "x" 1), atac 1, 
    (eres_inst_tac [("x", "%ns. Term ns : A state")] allE 1),
    (eres_inst_tac [("x", "state")] allE 1), etac impE 1, Auto_tac]) ;

val _ = qed_goalw "wpm_defc" Dmng.thy 
  [meta_eq_def, wpm_def, liftand, trmm_def, wlpm_def]
  "wpm C B state == (C state <= Term ` Collect B)"
  (fn _ => [Safe_tac, (case_tac "x" 1), Auto_tac]) ;

val _ = qed_goalw "totcref_alt" Dmng.thy 
  [meta_eq_def, totcref_def, wpm_def, liftand, liftimp, wlpm_def, trmm_def]
  "totcref A B == (ALL s. B s <= A s | NonTerm : A s)" 
  (fn _ => [Safe_tac, (case_tac "x" 1), 
    (eres_inst_tac [("x", "%ns. True")] allE 1),
    (eres_inst_tac [("x", "%ns. ns ~= sa")] allE 2),
    (ALLGOALS (eres_inst_tac [("x", "s")] allE)), Auto_tac]) ;

(** section 4 - sequential composition **)

val _ = qed_goal "seq_wlp" Dmng.thy 
  "wlpm (seq A B) Q = (wlpm A (wlpm B Q))" 
  (fn _ => [ (rtac ext 1), rewtac wlpm_def, Safe_tac,
    (etac allE 1), (etac impE 1), 
    (eatac seqIT 1 1), (etac seqE 2), Auto_tac]) ;

val _ = qed_goal "seq_trm" Dmng.thy 
  "trmm (seq A B) = (trmm A && wlpm A (trmm B))" 
  (fn _ => [ rtac ext 1, rewrite_goals_tac [liftand, wlpm_def, trmm_def],
    Safe_tac, (etac seqE 3), 
    (TRYALL (etac notE THEN' (fast_tac (ces seq.intros)))) ]) ;

val _ = qed_goal "seq_trm'" Dmng.thy 
  "trmm (seq A B) = wpm A (trmm B)" 
  (fn _ => [rtac ext 1, 
    (simp_tac (esimps [seq_trm, wpm_def]) 1), Fast_tac 1]) ;

val _ = qed_goal "seq_wp" Dmng.thy 
  "wpm (seq A B) Q = (wpm A (wpm B Q))" 
  (fn _ => [ (rtac ext 1), 
    (simp_tac (esimps [wpm_def, wlpm_conj, seq_trm, seq_wlp]) 1),
    (Fast_tac 1)]) ;

val seq_term = meta_std (prove_goal Dmng.thy
  "(ALL st. NonTerm ~: A st) & (ALL st. NonTerm ~: B st) --> \
    \ NonTerm ~: seq A B state"
  (fn _ => [(auto_tac cs_mng), (case_tac "x" 1), Auto_tac])) ;
    
val _ = qed_goal "seq_abort" Dmng.thy "seq abort A = abort" ft_mng ;
val _ = qed_goal "seq_magic" Dmng.thy "seq magic A = magic" ft_mng ;
val _ = qed_goal "pma" Dmng.thy "seq perhaps magic = abort" ft_mng ;

(** section 11 - refinement **)

val _ = qed_goalw "gencref_alt" Dmng.thy 
  [gencref_def, liftimp, trmm_def, partcref_alt]
  "gencref A B == (ALL state. B state <= A state)"
  (fn _ => [ (rtac eq_reflection 1), Fast_tac 1]) ;

val _ = qed_goalw "gencref_refl" Dmng.thy [gencref_alt] "gencref A A" ft_mng ;
AddIffs [gencref_refl] ;
    
val _ = qed_goalw_spec_mp "gencref_antisym" Dmng.thy [gencref_alt]
  "gencref A B --> gencref B A --> A = B" 
  (fn _ => [Safe_tac, rtac ext 1, Auto_tac]) ;
    
fun mk_sym def = prove_goal Dmng.thy "(?A :: bool) = ?B"
  (fn _ => [ (rtac (trans RS trans) 1), (rtac conj_commute 2),
    (rtac sym 2), (ALLGOALS (rtac (def RS def_imp_eq))) ]) ;

val _ = bind_thm ("totceqv_sym", mk_sym totceqv_def) ;

val _ = qed_goalw_spec_mp "totcref_trans" Dmng.thy [totcref_def, liftimp]
  "totcref A B --> totcref B C --> totcref A C" fn_ft1 ; 
    
val _ = qed_goalw_spec_mp "totceqv_trans" Dmng.thy [totceqv_def]
  "totceqv A B --> totceqv B C --> totceqv A C" 
  (fn _ => [ (fast_tac (ces [totcref_trans]) 1) ]) ;
    
val _ = qed_goalw_spec_mp "totceqv_alt" Dmng.thy 
  [meta_eq_def, totceqv_def, totcref_alt]
  "totceqv A B == (ALL s. A s = B s | NonTerm : A s Int B s)" fn_at ;
    
val _ = qed_goalw "gencref_def'" Dmng.thy 
  [meta_eq_def, gencref_alt, totcref_alt, partcref_alt]
  "gencref A B == (partcref A B & totcref A B)" fn_ft1 ;

val _ = qed_goalw "tref_term" Dmng.thy [totcref_def, partcref_def]
  "totcref (terms A) (terms B) = partcref A B"
  (fn _ => [ (simp_tac (esimps [wpm_term]) 1) ]) ;

val _ = qed_goalw "pref_term" Dmng.thy [totcref_def, partcref_def]
  "partcref (terms A) (terms B) = partcref A B"
  (fn _ => [ (simp_tac (esimps [wlpm_term]) 1) ]) ;

val _ = qed_goalw "gref_term" Dmng.thy [gencref_def']
  "partcref A B = gencref (terms A) (terms B)"
  (fn _ => [ (simp_tac (esimps [tref_term, pref_term]) 1) ]) ;

val _ = qed_goalw "gref_ntany" Dmng.thy [totcref_alt, gencref_alt]
  "totcref A B = gencref (ntany A) (ntany B)" ft_mng ;

val _ = qed_goalw "teqv_ntany" Dmng.thy [totceqv_def] "totceqv (ntany A) A" 
  (fn _ => [ (simp_tac (esimps [gref_ntany]) 1) ]) ;

val _ = qed_goalw_spec_mp "egMil_antisym" Dmng.thy [egMil_def]
  "egMil A B --> egMil B A --> A = B" 
  (fn _ => [Safe_tac, rtac gencref_antisym 1, 
    (auto_tac (cesimps [gencref_def']))]) ;
    
val _ = qed_goalw_spec_mp "seq_ref_mono" Dmng.thy [gencref_alt]
  "gencref A1 B1 --> gencref A2 B2 --> gencref (seq A1 A2) (seq B1 B2)"
  (fn _ => [Safe_tac, etac seqE 1, hyp_subst_tac 1, 
    rtac seqINT 1, rtac seqIT 2, Auto_tac]) ;

val _ = qed_goalw_spec_mp "seq_tref_mono" Dmng.thy [totcref_def]
  "totcref A1 B1 --> totcref A2 B2 --> totcref (seq A1 A2) (seq B1 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [seq_wp]) 1),
    (rtac wpm_mono_cond' 1), REPEAT (Force_tac 1) ]) ;

val _ = qed_goalw_spec_mp "seq_pref_mono" Dmng.thy [partcref_def]
  "partcref A1 B1 --> partcref A2 B2 --> partcref (seq A1 A2) (seq B1 B2)"
  (fn _ => [ (clarsimp_tac (cesimps [seq_wlp]) 1),
    (rtac wlpm_mono_cond' 1), REPEAT (Force_tac 1) ]) ;

(** strongest postconditions, see Lermer, Fidge, Hayes, CATS 2003 *)

val _ = qed_goal "slpm_slps" Dmng.thy 
  "Collect (slpm A Q) = slps A (Collect Q)" 
  (fn _ => [ (rtac set_ext 1), (simp_tac (esimps [slpm_def, slps_def]) 1) ]) ;

(* Thm 6.1 (vii) *)
val _ = qed_goal "wlp_slp_ref" Dmng.thy "partcref = slpref"
  (fn _ => [ (REPEAT (rtac ext 1)), 
  (rewrite_goals_tac [partcref_def, slpref_def, liftimp, wlpm_def, slpm_def]),
  Fast_tac 1]) ;

val _ = qed_goal "seq_slp" Dmng.thy "slpm (seq A B) Q = slpm B (slpm A Q)"
  (fn _ => [ (rtac ext 1), rewtac slpm_def, Safe_tac,
    (fast_tac (claset () addSEs [seqIT]) 2),
    (etac seqE 1), Auto_tac]) ;

val _ = qed_goal "spom_alt" Dmng.thy 
  "Collect (spom C B) = UNION (Collect B) C"
  (fn _ => [ (rtac set_ext 1), (simp_tac (esimps [spom_def]) 1)]) ;

(** the Galois connection, Lermer, Fidge, Hayes, CATS 2003, Thm 6.1,
  Dunne calls this the Slide Rule **)

val _ = qed_goalw "wlp_slp_gal" Dmng.thy [liftimp, wlpm_def, slpm_def]
  "(Q ---> wlpm C R) = (slpm C Q ---> R)" (fn _ => [Fast_tac 1]) ;

(* Thm 6.1 (v), (vi) *)
val [th61v, th61vi] = [liftimp_refl] RL ([wlp_slp_gal] RL [iffD1, iffD2]) ;

val ss = simpset () delsimps [liftimp] ;

val _ = qed_goal "wlp_slp_ref_eqv" Dmng.thy 
  "(wlpm A = wlpm B) = (slpm A = slpm B)"
  (fn _ => [ Safe_tac, 
    (ALLGOALS (rtac (liftimp_antisym RS ext))),
    (ALLGOALS (resolve_tac ([wlp_slp_gal] RL [iffD1, iffD2]))),
    (TRYALL (asm_simp_tac ss THEN' resolve_tac [th61v, th61vi])),
    (TRYALL (dtac sym THEN'
      asm_simp_tac ss THEN' resolve_tac [th61v, th61vi]))]) ;
    
(** outcome-based pre/post-conditions **)

fun ftacwws _ = [ (rtac ext 1), 
  (simp_tac (esimps [wpom_def, wpm_def, wlpm_def, trmm_def]) 1),
  Safe_tac, (case_tac "oc" 1), Auto_tac] ;

val _ = qed_goal "wp_wpo" Dmng.thy 
  "wpm C Q = wpom C (%oc. oc : Term ` Collect Q)" ftacwws ;

val _ = qed_goal "wlp_wpo" Dmng.thy 
  "wlpm C Q = wpom C (%oc. oc : insert NonTerm (Term ` Collect Q))" ftacwws ;

(*
val _ = qed_goal "trm_wpo" Dmng.thy 
  "trmm C = wpom C (range Term%)" ftacwws ;
  *)
  

val _ = qed_goal "slp_spo" Dmng.thy 
  "slpm C Q = spom C Q o Term" 
  (fn _ => [ (rtac ext 1), (simp_tac (esimps [spom_def, slpm_def]) 1)]) ;
     
val _ = qed_goalw "wpo_spo_gal" Dmng.thy [liftimp, wpom_def, spom_def]
  "(Q ---> wpom C R) = (spom C Q ---> R)" (fn _ => [Fast_tac 1]) ;

(* alternative characterisation of (Q ---> wpom C R) *)
val _ = qed_goalw "wpo_gal_alt" Dmng.thy [liftimp, wpom_def]
  "(Q ---> wpom C R) = (svf2rel C `` Collect Q <= Collect R)"
  (fn _ => [ Safe_tac, (dtac subsetD 2), (rtac ImageI 2), Auto_tac]) ;

val _ = qed_goalw "gencref_wpo" Dmng.thy [liftimp, gencref_alt, wpom_def]
  "gencref A B = (ALL Q. wpom A Q ---> wpom B Q)" fn_ft1 ;

val _ = qed_goalw "gencref_spo" Dmng.thy [liftimp, gencref_alt, spom_def]
  "gencref A B = (ALL Q. spom B Q ---> spom A Q)" fn_ft1 ;

(* relevant to Dunne's A Theory of Generalised Substitutions.
  ZB2002, LNCS 2272, 270-290 in which two commands are equal if they have the
  same wp and same frame *)
(* actually this should follow easily from totcref_alt *)

val _ = qed_goal "wp_eq" Dmng.thy "(ALL Q. wpm A Q = wpm B Q) = \
  \ (trmm A = trmm B & (ALL s. trmm A s --> A s = B s))"
  (fn _ => [ Safe_tac,
    (asm_simp_tac (esimps [wp_trm]) 1), 
    (rtac ext 3), 
    (eres_inst_tac [("x", "x")] allE 3),
    (dres_inst_tac [("x", "x")] fun_cong 3), 
    (force_tac (cesimps defs_mng) 3),
    (REPEAT (EVERY [
      (subgoal_tac "trmm B s" 1), 
      (force_tac (cesimps [wp_trm]) 2),
      (case_tac "x" 1), 
      (force_tac (cesimps defs_mng) 1),
      (eres_inst_tac [("x", "%s. s ~= sa")] allE 1),
      (dres_inst_tac [("x", "s")] fun_cong 1), 
      (force_tac (cesimps defs_mng) 1)])) ]) ;


