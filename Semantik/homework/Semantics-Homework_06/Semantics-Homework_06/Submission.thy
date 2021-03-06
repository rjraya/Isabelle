theory Submission
  imports Defs 
begin

(* Exercise 1 *)

definition "square \<equiv> 
  ''z'' ::= N 1;;
  ''a'' ::= N 0;;
   WHILE Less (N 0) (V ''n'') DO (
     ''a'' ::= Plus (V ''a'') (V ''z'');;
     ''z'' ::= Plus (V ''z'') (N 2);; 
     ''n'' ::= Plus (V ''n'') (N (-1))
   )"

theorem square_correct: "s ''n'' \<equiv> n \<Longrightarrow> n \<ge> 0 \<Longrightarrow> wlp square (\<lambda>s'. let a = s' ''a'' in a = n*n) s"
  unfolding square_def
  apply(smartvcg)
  apply(subst wlp_annotate_while[
        where I = "\<lambda>s'. s' ''n'' \<ge> 0 \<and>  
                        s' ''z'' = 2*(s ''n'' - s' ''n'') + 1 \<and>
                        s' ''a'' = (s ''n'' - s' ''n'')*(s ''n'' - s' ''n'')"  ])
  apply(smartvcg)
  apply(auto simp add: algebra_simps)
done

(* Exercise 2 *)

fun cfg_step :: "com * state \<Rightarrow> com * state" where
  "cfg_step (SKIP,s) = (SKIP,s)"
| "cfg_step (x ::= a,s) = (SKIP,s(x := aval a s))"
| "cfg_step (SKIP ;; c2, s) = (c2, s)"
| "cfg_step (c1 ;; c2, s) = (let (c1',s') = cfg_step (c1,s) in (c1' ;; c2,s'))"
| "cfg_step (IF b THEN c1 ELSE c2, s) = (if bval b s then (c1,s) else (c2,s))"
| "cfg_step (WHILE b DO c, s) = (IF b THEN c ;; (WHILE b DO c) ELSE SKIP, s)"

lemma small_induction: "c1 \<noteq> SKIP \<Longrightarrow> (c1,s) = cs \<Longrightarrow> (c1',s') = cs' \<Longrightarrow>
       cfg_step cs = cs' \<Longrightarrow> cfg_step (c1 ;; c2, s) = (c1' ;; c2,s')"
  apply(induction cs rule: cfg_step.induct)
  apply(auto)
done

theorem small_step_cfg_step: "cs \<rightarrow> cs' \<Longrightarrow> cfg_step cs = cs'"
proof(induction rule: small_step.induct)
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  note prems = this
  then have distinct: "c\<^sub>1 \<noteq> SKIP" by auto
  from prems distinct have 
   "cfg_step (c\<^sub>1 ;; c\<^sub>2,s) = (c\<^sub>1' ;; c\<^sub>2,s')" by (simp add: small_induction)
  from this prems show ?case by auto
qed auto+

theorem final_cfg_step: "final cs \<Longrightarrow> cfg_step cs = cs"
  unfolding final_def
  by (metis cfg_step.simps(1) finalD final_def old.prod.exhaust)
  
fun cfg_steps :: "nat \<Rightarrow> com * state \<Rightarrow> com * state" where
  "cfg_steps 0 cs = cs" |
  "cfg_steps (Suc n) cs = cfg_steps n (cfg_step cs)"

lemma  small_steps_cfg_steps_aux: "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<exists>n. cfg_steps n (c,s) = (c',s')"
proof(induction rule: star_induct)
  case refl
  from this cfg_steps.simps(1) show ?case by blast
next
  case (step a b a b)
  then show ?case by (metis cfg_steps.simps(2) small_step_cfg_step)
qed

theorem small_steps_cfg_steps:
  "cs \<rightarrow>* cs' \<Longrightarrow> \<exists>n. cfg_steps n cs = cs'"
  by (metis small_steps_cfg_steps_aux surj_pair)

theorem cfg_steps_small_steps:
  "cfg_steps n cs = cs' \<Longrightarrow> cs \<rightarrow>* cs'"
proof(induction n cs arbitrary: cs' rule: cfg_steps.induct)
  case (2 n cs)
  then show ?case 
    by (metis cfg_steps.simps(2) converse_rtranclp_into_rtranclp 
        final_cfg_step final_def small_step_cfg_step) 
qed auto+

corollary cfg_steps_correct:
  "cs \<rightarrow>* cs' \<longleftrightarrow> (\<exists>n. cfg_steps n cs = cs')"
  by (metis small_steps_cfg_steps cfg_steps_small_steps)

(* Exercise 3 *)

definition
  "is_sim R step step' \<equiv> \<forall>a b a'. R a b \<and> step a a' \<longrightarrow> (\<exists>b'. R a' b' \<and> step' b b')"

lemma star_aux:
 "step\<^sup>*\<^sup>* a a' \<Longrightarrow> is_sim R step step' \<Longrightarrow> R a b \<Longrightarrow> \<exists>b'. R a' b' \<and> step'\<^sup>*\<^sup>* b b'"
  apply(simp add: is_sim_def)
  apply(induction rule: rtranclp_induct)
  apply blast
  by (metis rtranclp.rtrancl_into_rtrancl)

lemma is_sim_star:
  assumes "is_sim R step step'" "R a b" "step\<^sup>*\<^sup>* a a'"
  shows "\<exists>b'. R a' b' \<and> step'\<^sup>*\<^sup>* b b'"
  by (meson assms(1) assms(2) assms(3) star_aux)

inductive terminating for step where
 "(\<And> s'. step s s' \<Longrightarrow> terminating step s') \<Longrightarrow> terminating step s"

theorem terminating_induct:
  assumes major: "terminating r a"
  assumes hyp: "\<And>x. terminating r x \<Longrightarrow> \<forall>y. r x y \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  apply (rule major [THEN terminating.induct])
  apply (rule hyp)
  apply (auto simp add: terminating.intros)
  done

definition "P step step' R b \<longleftrightarrow> (\<forall> a. R a b \<longrightarrow> terminating step a)"

lemma terminating_step: "is_sim R step step' \<Longrightarrow> terminating step' x \<Longrightarrow> 
       \<forall> y. step' x y \<longrightarrow> P step step' R y \<Longrightarrow> P step step' R x"
proof(simp add: P_def)
  assume c1: "terminating step' x"and
         i1: "\<forall>y. step' x y \<longrightarrow> (\<forall>a. R a y \<longrightarrow> terminating step a)" and
         sim: "is_sim R step step'"
  show "\<forall>a. R a x \<longrightarrow> terminating step a"
  proof
    fix a
    show "R a x \<longrightarrow>terminating step a"
    proof 
      assume c2: "R a x"
      show "terminating step a"
      proof
        fix s'
        assume s1: "step a s'"
        from c1 c2 s1 sim have "\<exists>b'. R s' b' \<and> step' x b'" by (metis is_sim_def)
        then obtain b' where s'1: "R s' b' \<and> step' x b'" by auto
        from c1 s'1 i1 have "terminating step s'" by blast
        show "terminating step s'" by (simp add: \<open>terminating step s'\<close>)
      qed
    qed
  qed
qed

lemma simulation_aux: "terminating step' b \<Longrightarrow> is_sim R step step' \<Longrightarrow> R a b \<Longrightarrow> terminating step a"
proof - 
  assume 0: "terminating step' b"
  assume 1: "is_sim R step step'"
  assume 2: "R a b"
  from terminating_induct[of "step'" "b" "P step step' R"] terminating_step have
   "P step step' R b" by (metis (no_types, lifting) "0" "local.1")
  thus "terminating step a" by (simp add: "2" P_def)
qed

theorem terminating_simulation:
  assumes "is_sim R step step'" "terminating step' b" "R a b"
  shows "terminating step a"
  by (meson assms(1) assms(2) assms(3) simulation_aux)

(* Exercise 4 *)

theorem wlp_whileI':
  assumes INIT: "I s\<^sub>0"
  assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp c I s else Q s)"
  shows "wlp (WHILE b DO c) Q s\<^sub>0"
  unfolding wlp_def 
  proof clarify 
    fix t 
    show "(WHILE b DO c, s\<^sub>0) \<Rightarrow> t \<Longrightarrow> Q t" 
      by(insert INIT ; 
        induction "WHILE b DO c" s\<^sub>0 t rule: big_step_induct ; 
        (meson  STEP  wlp_def)+ )  
  qed

(*
 (* Not the shortest, but pure script style *)

 theorem wlp_whileI'1:
  assumes INIT: "I s\<^sub>0"
  assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp c I s else Q s)"
  shows "wlp (WHILE b DO c) Q s\<^sub>0"
  apply(unfold wlp_def; clarify)
  subgoal for t 
  by(insert INIT  ; 
     induction "WHILE b DO c" s\<^sub>0 t rule: big_step_induct ;
     (meson assms wlp_def)+ ) 
  done
*)

end