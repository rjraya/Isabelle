
structure Dunb = struct val thy = theory "Dunb" end ;
val _ = use_legacy_bindings Dunb.thy ;

fun utu() = update_thy "Dunb" ;
fun utou() = update_thy_only "Dunb" ;
fun uu() = use "Dunb.ML" ;

val unb_term = prove_goal Dunb.thy 
  "ALL state. NonTerm ~: rep n (unb x) state"
   (fn _ => [(induct_tac "n" 1), 
     (auto_tac (claset () addSEs [seqE], esimps [unitos_def])),
     (etac thin_rl 1), rewtac unb_def, 
     (asm_full_simp_tac (simpset () addsplits [split_if_asm]) 1),
     (auto_tac (cesimps [choice_def, assignv_def]))]) RS spec ;

val unb_rep = meta_std (prove_goal Dunb.thy 
  "state x = Suc n & m <= n --> \
    \ rep m (unb x) state = assign x (Suc n - m) state"
   (fn _ => [(induct_tac "m" 1), 
     (simp_tac (esimps [unitos_def, assignv_def]) 1),
     rtac impI 1, rtac ext 1, Force_tac 1,
     (Clarify_tac 1), 
     (asm_simp_tac (init_ss addsimps [rep_Suc']) 1),
     etac impE 1, arith_tac 1,
     (asm_simp_tac (esimps (unb_def :: assignv_def :: defs_mc)) 1),
     Safe_tac, arith_tac 1, rtac ext 1, Simp_tac 1])) ;

val unb_rep' = prove_goal Dunb.thy 
  "state x = Suc n --> rep (Suc n) (unb x) state = {}"
  (fn _ => [rtac impI 1, dtac unb_rep 1, rtac le_refl 1,
     (simp_tac (init_ss addsimps [rep_Suc']) 1),
     (asm_simp_tac (esimps (unb_def :: assignv_def :: defs_mc)) 1)]) RS mp ;

val unb_infch' = prove_goalw Dunb.thy [infch_def]
  "0 < state x --> ~ infch (unb x) state"
  (fn _ => [Safe_tac, 
    (subgoal_tac "ALL n m. Term (f (m + n)) : rep m (unb x) (f n)" 1),  
    (rtac allI 2), (rtac allI 2), (induct_tac "m" 2),
    (simp_tac (esimps [unitos_def]) 2),
    (simp_tac (init_ss addsimps [rep_Suc']) 2), 
    etac seqIT 2, etac spec 2,
    (dtac (Suc_pred RS sym) 1), dtac unb_rep' 1, 
    etac thin_rl 1, 
    (eres_inst_tac [("x", "0")] allE 1),
    (full_simp_tac init_ss 1), Fast_tac 1]) RS mp ;

val unb_infch = prove_goal Dunb.thy "~ infch (unb x) state"
  (fn _ => [(case_tac "state x" 1), 
    rtac notI 1, dtac infch_prev 1, Safe_tac,
    (subgoal_tac "0 < nst x" 1), 
    (full_simp_tac (esimps [unb_def, choice_def, assignv_def] 
      addsplits [split_if_asm]) 2),
    Force_tac 2, 
    (ALLGOALS (etac (rotate_prems 1 (unb_infch' RS notE)))), Auto_tac]) ;

val unb_trm = prove_goalw Dunb.thy [trmm_def, repstar_def]
  "trmm (repstar (unb x)) state"
  (fn _ => [
    (simp_tac (esimps [unb_infch]) 1),
    (rtac repall_term 1), 
    (simp_tac (esimps [unb_def, choice_def, assignv_def]) 1)]) ;

val unb_cic0 = prove_goalw Dunb.thy [cic_def, fis_def]
  "state x = 0 --> cic (unb x) state"
  (fn _ => [Safe_tac, (case_tac "n" 1), 
    (ALLGOALS (asm_full_simp_tac (esimps [unitos_def]))),
    (dtac equals0D 1), etac notE 1, 
    (res_inst_tac [("s1.0", "assign' x n state")] seqIT 1), 
    (rtac (unb_rep RS set_cong RS iffD2) 2), 
    rtac le_refl 3, (simp_tac (esimps [assignv_def]) 3),
    (ALLGOALS (asm_simp_tac (esimps 
      [unb_def, choice_def, assign'_def, assignv_def]))),
    Fast_tac 1]) RS mp ;

