theory Wp
  imports "Main" Syntax Big_step Small_step Termination
begin

section \<open>Weakest preconditions\<close>

text\<open> 
 The definition of weakest precondition has to be modified.
 The first conjunct states that the command terminates.
 The second conjunct states that for any possible terminating state,
 the postcondition holds. 

 Note that we as Dijkstra, focus on weakest preconditions. There is 
 also a theory for the weakest liberal precondition but we will not use
 it in the future.
\<close>

definition "wp c Q s \<equiv> terminating (c,s) \<and> (\<forall> t'. (c,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> Q t')"

subsection \<open>Basic properties\<close>

text \<open>
 Law of excluded miracle.
 Started in a given state, a program execution must 
 either terminate or loop forever.
\<close>

lemma excluded_miracle: "wp c (\<lambda> t. False) = (\<lambda> s. False)" 
  unfolding wp_def by (meson must_imp_may)

text \<open>Strengthening of postcondition\<close>

lemma post_strengthen: "wp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wp c Q s" 
  using wp_def by auto

lemma post_conjunction: "((wp c P s) \<and> (wp c Q s)) = wp c (\<lambda> r. P r \<and> Q r) s"
  unfolding wp_def by auto

text \<open>
 The following property would be an equivalence for non-deterministic languages.
 In non-deterministic languages only one implication can be proved:
\<close>

lemma post_disjunction: "(wp c P s) \<or> (wp c Q s) \<Longrightarrow> wp c (\<lambda> r. P r \<or> Q r) s"
  unfolding wp_def by auto

subsection \<open>Weakest preconditions equations\<close>

text \<open>We establish the semantics of the different commands:\<close>

lemma wp_skip_eq: "wp SKIP Q s = Q s" unfolding wp_def 
  by (simp add: Skip_simp skip_terminates)
lemma wp_assign_eq: "wp (x::=a) Q s = Q (s(x:=aval a s))" unfolding wp_def 
  using assign_terminates by auto
lemma wp_if_eq: "wp (IF gcs FI) Q s = (BB gcs s \<and> (\<forall> b c. ((b,c) \<in> set gcs \<and> bval b s) \<longrightarrow> wp c Q s))"
  unfolding wp_def using if_terminates by auto

text \<open>
 The hard work has been done in the Termination theory, so here the proof of 
 the sequential equation is easy.
\<close>

lemma wp_seq_eq: "wp (c1;;c2) Q s = wp c1 (wp c2 Q) s"
  unfolding wp_def
  apply(rule iffI)
   apply (meson Seq_simp seq_termination seq_termination_2)
  by (meson Seq_simp must_imp_may seq_termination_imp_2)

subsection \<open>Weakest precondition for do\<close>

text \<open> 
 We follow Dijkstra's approach, defining exactly the same function H which essentially
 counts the number of iterations the DO construction has been executed. The proof of 
 wp_do_imp_2 presents the future of having to use the choice operator SOME which we only
 saw in the last class of the course. 
\<close>

fun H :: "nat \<Rightarrow> (bexp \<times> com) list \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool" where
"H 0 gcs Q s = ((Q s) \<and> \<not> (BB gcs s))" |
"H (Suc n) gcs Q s  = 
  ((wp (IF gcs FI) (H n gcs Q) s) \<or> (H 0 gcs Q s))"

text \<open>
 We need this property to take the maximum of the number of iterations that we obtain
 on each branch from a given node. 
\<close>

lemma H_monotone: 
  "H k gcs Q s \<Longrightarrow> 
       k' \<ge> k \<Longrightarrow> 
       H k' gcs Q s"
  apply(induction k arbitrary: s k' Q)
  using H.elims(3) apply blast
  using Suc_less_eq2 wp_def 
  by (smt H.simps(2) Suc_le_D less_eq_nat.simps(2) nat.case(2))

lemma wp_do_1: "
 H k gcs Q s \<Longrightarrow> (DO gcs OD, s) \<Rightarrow>\<^sub>g t \<Longrightarrow> Q t
" 
proof(induction k gcs Q s rule: H.induct)
  case (1 gcs Q s)
  then have "Q s" by simp
  moreover have "t = s" using BB_def "1" by force
  ultimately show ?case by simp
next
  case (2 n gcs Q s)
  then show ?case 
  by (smt BB_def H.simps(2) SeqE com.distinct(7) sDoWhileE seq_terminating_3 wp_def wp_if_eq)     
qed
 
lemma wp_do_2: "H k gcs Q s \<Longrightarrow> terminating (DO gcs OD, s)"
 proof(induction k gcs Q s rule: H.induct)
   case (1 gcs Q s)
then show ?case 
  by (simp add: do_termination_1) 
next
  case (2 n gcs Q s)
  then have 0: "(wp (IF gcs FI) (H n gcs Q) s) \<or> (H 0 gcs Q s)" by simp
  then have 1: "(terminating ((IF gcs FI),s) \<and> 
             (\<forall> t'. ((IF gcs FI),s) \<Rightarrow>\<^sub>g t' \<longrightarrow> (H n gcs Q) t')) \<or>
             (H 0 gcs Q s)" 
    by (simp add: wp_def)
  have 2: "(DO gcs OD,s) \<rightarrow>\<^sub>g (SKIP,s) \<or> 
        (\<exists> b c. (b,c) \<in> set gcs \<and> bval b s \<and> (DO gcs OD,s) \<rightarrow>\<^sub>g (c;;DO gcs OD,s))"
    by blast
  have 3: "terminating(SKIP,s)" by (simp add: skip_terminates)
  {
    fix b c
    assume 5: "(b,c) \<in> set gcs \<and> bval b s \<and> (DO gcs OD,s) \<rightarrow>\<^sub>g (c;;DO gcs OD,s)"
    have "terminating (c;; DO gcs OD,s)" 
    proof -
      have 6: "terminating (c,s)" 
        by (meson "1" "2.IH"(2) "5" IfTrue seq_termination_1 terminating.cases)
      have 7: "\<forall>t. (c, s) \<Rightarrow>\<^sub>g t \<longrightarrow> terminating (DO gcs OD, t)" 
        by (meson "1" "2.IH"(1) "2.IH"(2) "5" IfBlock seq_termination_2 terminating.cases)
      have 8: "\<exists>t. (c, s) \<Rightarrow>\<^sub>g t \<and> terminating (DO gcs OD, t)"
        using "6" "7" must_imp_may by blast
      show "terminating (c;;DO gcs OD,s)" 
        by (simp add: "6" "7" "8" seq_termination_imp_2)
    qed
  }
  note case2 = this
  then show ?case 
    by (metis (full_types) sDoWhileE skip_terminates terminating.intros)  
qed

lemma wp_do_imp_1: "(\<exists> k. H k gcs Q s) \<Longrightarrow> wp (DO gcs OD) Q s"
  unfolding wp_def
  apply(rule conjI)
  using wp_do_2 apply blast
  using wp_do_1 by blast

lemma do_progress: "
(DO gcs OD,s) \<rightarrow>\<^sub>g (c;;DO gcs OD,s) \<Longrightarrow> (c,s) \<Rightarrow>\<^sub>g t' \<Longrightarrow>
 (DO gcs OD,s) \<rightarrow>\<^sub>g+ (DO gcs OD,t')" 
proof -
  assume 0: "(DO gcs OD,s) \<rightarrow>\<^sub>g (c;;DO gcs OD,s)"
  assume 1: "(c,s) \<Rightarrow>\<^sub>g t'"
  then have 2: "(c,s) \<rightarrow>\<^sub>g* (SKIP,t')" by (simp add: big_to_small)
  then have 3: "(c;;DO gcs OD,s) \<rightarrow>\<^sub>g* (DO gcs OD,t')" 
    by (meson Seq1 rtranclp.simps star_seq2)
  then show "(DO gcs OD,s) \<rightarrow>\<^sub>g+ (DO gcs OD,t')" using "0" by auto
qed

lemma do_skip_h:
  "(DO gcs OD,s) \<rightarrow>\<^sub>g (SKIP,s) \<Longrightarrow>
   (\<forall>t'. (DO gcs OD,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> Q t') \<Longrightarrow>
   H 0 gcs Q s"
proof -
  assume 0: "(DO gcs OD,s) \<rightarrow>\<^sub>g (SKIP,s)"
  assume 1: "(\<forall>t'. (DO gcs OD,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> Q t')"
  have 2: "\<not> BB gcs s" using "0" BB_def by fast
  have 3: "Q s" using "0" "1" by fast
  from "2" "3" show ?thesis by simp
qed

lemma wp_do_imp_2: "
 terminating' (DO gcs OD, s) \<Longrightarrow>
 (\<forall>t'. (DO gcs OD,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> Q t') \<Longrightarrow>
 (\<exists> k. H k gcs Q s)"
proof(induction "(DO gcs OD,s)" arbitrary: s rule: terminating'.induct)
  case 1
  then show ?case 
  proof -
  have t: "terminating' (DO gcs OD, s)" 
    by (simp add: "1.hyps"(1) terminating'.intros)
  have 0: "(\<forall>t'. (DO gcs OD,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> Q t')" 
    by (simp add: "1.prems")
  have 2: "(DO gcs OD,s) \<rightarrow>\<^sub>g (SKIP,s) \<Longrightarrow> H 0 gcs Q s"
    using "1.prems" do_skip_h by blast
  have 3: "\<forall> c t'. (DO gcs OD,s) \<rightarrow>\<^sub>g (c;;DO gcs OD,s) \<longrightarrow> 
                (c,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> 
                (\<exists>k. H k gcs Q t')"
    by (meson "1.hyps"(2) "1.prems" Seq_simp do_progress small1_big_continue)
  
  from "3" have 
    5: "\<forall> b c. (b,c) \<in> set gcs \<longrightarrow> bval b s \<longrightarrow>
          (\<forall> t. (c,s) \<Rightarrow>\<^sub>g t \<longrightarrow> (\<exists>k. H k gcs Q t))" by blast

  {assume 6: "\<not> H 0 gcs Q s"
  from "t" "6" have 7: "terminating (IF gcs FI,s)" 
    by (meson "2" BB_def do_termination_2 gsmall_step.DoFalse trans_terminating)
  from "5" "6" H_monotone have 
   8: "\<forall> t'. (IF gcs FI,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> (\<exists> k. (H k gcs Q) t')" by blast
  have 9: "finite {t'.(IF gcs FI,s) \<Rightarrow>\<^sub>g t'}"  
       by (simp add: "7" finite_terminating)
  obtain k where 10: "k = Max ((\<lambda> t. SOME k. (H k gcs Q) t) ` ({t'.(IF gcs FI,s) \<Rightarrow>\<^sub>g t'}))"
    by blast
  have 13:"(\<forall> t'. (IF gcs FI,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> (H k gcs Q t'))" 
  proof(intro allI impI)
    fix t'
    assume "(IF gcs FI,s) \<Rightarrow>\<^sub>g t'"
    show "H k gcs Q t'"
    proof -
      let ?A = "((\<lambda> t. SOME k. (H k gcs Q) t) ` ({t'.(IF gcs FI,s) \<Rightarrow>\<^sub>g t'}))"
      let ?B = "{t'. (IF gcs FI, s) \<Rightarrow>\<^sub>g t'}"
      let ?f = "(\<lambda>t. SOME k. H k gcs Q t)"
      have 11: "\<forall> k' \<in> ?f `?B. k' \<le> k" by (simp add: "10" "9")               
      have 12: "\<forall> t'. (IF gcs FI,s) \<Rightarrow>\<^sub>g t' \<longrightarrow> (\<exists> k' \<in> ?f ` ?B. H k' gcs Q t')"
       by (meson "8" imageI mem_Collect_eq tfl_some)
      show "H k gcs Q t'" 
       using "11" "12" H_monotone \<open>(IF gcs FI, s) \<Rightarrow>\<^sub>g t'\<close> by blast
     qed
  qed
  from "7" this have "wp (IF gcs FI) (H k gcs Q) s" unfolding wp_def by simp
  then have "H (k+1) gcs Q s" by simp
  then have "\<exists> k. H k gcs Q s" by blast }
  then show ?case by blast
qed
qed

theorem wp_do_eq: "wp (DO gcs OD) Q s = (\<exists> k. H k gcs Q s)"
  unfolding wp_def
  apply(rule iffI)
  apply (simp add: trans_terminating wp_do_imp_2)
  using wp_do_1 wp_do_2 by blast

subsection \<open>Unfold lemma\<close>

text \<open>
 In this section we establish a similar result to the one we have for while loops
 in the IMP language. This will help us to write introduction rules for IF and DO
 and verify some programs in the theory Verify.
\<close>

lemma unfold_lemma_1: "terminating (IF gcs FI, s) \<Longrightarrow> BB gcs s \<Longrightarrow>
       (\<forall>t'. (IF gcs FI, s) \<Rightarrow>\<^sub>g t' \<longrightarrow> terminating (DO gcs OD, t')) \<Longrightarrow>
       (\<forall> t' t'a. (DO gcs OD, t') \<Rightarrow>\<^sub>g t'a \<longrightarrow> Q t'a) \<Longrightarrow>
       terminating (DO gcs OD, s) "
proof -
  assume 0: "terminating (IF gcs FI, s)"
  assume 1: "BB gcs s"
  assume 2: "\<forall>t'. (IF gcs FI, s) \<Rightarrow>\<^sub>g t' \<longrightarrow> terminating (DO gcs OD, t')" 
  
  have "\<And> b c. ((b,c) \<in> set gcs \<and> bval b s) \<Longrightarrow> terminating (c;;DO gcs OD,s)" 
  proof -
    fix b c
    assume "(b,c) \<in> set gcs \<and> bval b s"
    then show "terminating (c;;DO gcs OD,s)"
      by (meson "0" "2" IfBlock if_terminates must_imp_may seq_termination_imp_2)
  qed
  
  then show "terminating (DO gcs OD,s)" 
    by (metis "1" BB_def sDoWhileE terminating.simps)
qed

lemma unfold_lemma_2:
  assumes "(if BB gcs s
     then terminating (IF gcs FI, s) \<and>
          (\<forall>t'. (IF gcs FI, s) \<Rightarrow>\<^sub>g t' \<longrightarrow>
                terminating (DO gcs OD, t') \<and>
                (\<forall>t'a. (DO gcs OD, t') \<Rightarrow>\<^sub>g t'a \<longrightarrow> Q t'a))
     else Q s)"
  shows "terminating (DO gcs OD, s)" 
  using assms  by (metis curryI do_termination_1 unfold_lemma_1 wp_assign_eq wp_def)

lemma unfold_lemma_3:
 assumes "terminating (DO gcs OD, s)"
 assumes "\<forall>t'. (DO gcs OD, s) \<Rightarrow>\<^sub>g t' \<longrightarrow> Q t'"
 shows "
   (if BB gcs s
     then terminating (IF gcs FI, s) \<and>
          (\<forall>t'. (IF gcs FI, s) \<Rightarrow>\<^sub>g t' \<longrightarrow>
                terminating (DO gcs OD, t') \<and>
                (\<forall>t'a. (DO gcs OD, t') \<Rightarrow>\<^sub>g t'a \<longrightarrow> Q t'a))
     else Q s)
  " 
  using assms
  by (metis H.elims(2) H.simps(1) do_termination_2 wp_def wp_do_1 wp_do_2 
              wp_do_eq wp_if_eq)

lemma unfold_lemma_4:
  assumes "(if BB gcs s
     then terminating (IF gcs FI, s) \<and>
          (\<forall>t'. (IF gcs FI, s) \<Rightarrow>\<^sub>g t' \<longrightarrow>
                terminating (DO gcs OD, t') \<and>
                (\<forall>t'a. (DO gcs OD, t') \<Rightarrow>\<^sub>g t'a \<longrightarrow> Q t'a))
     else Q s)"
  assumes "(DO gcs OD, s) \<Rightarrow>\<^sub>g t'"
  shows "Q t'"
proof(cases "BB gcs s")
case True
  then show ?thesis 
  proof -
    obtain b c t where "(b,c) \<in> set gcs \<and> bval b s \<and> (c,s) \<Rightarrow>\<^sub>g t \<and> (DO gcs OD,t) \<Rightarrow>\<^sub>g t'"
      by (metis (full_types) BB_def SeqE True assms(2) com.distinct(7) sDoWhileE seq_terminating_3)
    then have 0: "(IF gcs FI, s) \<Rightarrow>\<^sub>g t \<and> (DO gcs OD,t) \<Rightarrow>\<^sub>g t'" by auto
    then have "(\<forall>t'a. (DO gcs OD, t) \<Rightarrow>\<^sub>g t'a \<longrightarrow> Q t'a)" using True assms by auto
    then show "Q t'" using "0" by simp
  qed
next
case False
  then show ?thesis using assms wp_do_1  by (metis H.simps(1)) 
qed

theorem wp_do_unfold: "wp (DO gcs OD) Q s =
  (if (BB gcs s) then wp (IF gcs FI) (wp (DO gcs OD) Q) s else Q s)"
  unfolding wp_def
  apply(rule iffI)
  using unfold_lemma_3 apply blast
  using unfold_lemma_2 unfold_lemma_4 by blast

end