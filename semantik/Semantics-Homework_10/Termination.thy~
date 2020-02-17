theory Termination
  imports "Main" Small_step Syntax Big_step
begin

text \<open>
 One of the difficulties that non-determinism creates, is the fact that termination
 does no longer depend on a single execution path. 
\<close>

section \<open>Definition and first properties\<close>

inductive terminating where
 "(\<And> s'. s \<rightarrow>\<^sub>g s' \<Longrightarrow> terminating s') \<Longrightarrow> terminating s"

text \<open>
 Termination with respect to \<open>\<rightarrow>\<^sub>g\<close> and to \<open>\<rightarrow>\<^sub>g+\<close> is equivalent. We need
 the second one if some of the proofs that deal with the do case. In particular,
 when one deduces (DO gcs OD,s) \<open>\<rightarrow>\<^sub>g\<close> (c;;DO gcs OD,s).

 Instead, we would like to know about what happens after executing c, since instantiating
 the indution rule with "(DO gcs OD,s)" will assume that all derivations are also of this form.
\<close>

inductive terminating' where
 "(\<And> s'. s \<rightarrow>\<^sub>g+ s' \<Longrightarrow> terminating' s') \<Longrightarrow> terminating' s"

lemma trans_terminating: "terminating s \<longleftrightarrow> terminating' s"
  apply(rule iffI)
  apply(induction rule: terminating.induct)
  apply(metis converse_tranclpE terminating'.simps)
  apply(induction rule: terminating'.induct)
  by (simp add: terminating.intros tranclp.r_into_trancl)

text \<open>
 We reused here the ideas we had in the exercise sheet 6. In fact, we realized
 that the induction principle provided by the terminating.induct formula is just
 as good as this rephrasing. However, we maintain it for the derivations that use
 it later. It could very well be refactored.
\<close>

theorem terminating_induct:
  assumes major: "terminating a"
  assumes hyp: "\<And>x. terminating x \<Longrightarrow> \<forall>y. x \<rightarrow>\<^sub>g y \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  apply (rule major [THEN terminating.induct])
  apply (rule hyp)
  apply (auto simp add: terminating.intros)
  done

text \<open>
 If small-step is terminating there is at least one terminating execution in the
 big-step. This very simple property let us progress for a while in the theory.
\<close>

lemma must_imp_may: "terminating (c,s) \<Longrightarrow> \<exists> t. (c,s) \<Rightarrow>\<^sub>g t"
proof -
  assume 0: "terminating (c,s)"
  let ?P = "\<lambda> y. \<exists> t. y \<Rightarrow>\<^sub>g t"
  have 1: "\<And>x. \<forall>y. x \<rightarrow>\<^sub>g y \<longrightarrow> ?P y \<Longrightarrow> ?P x"
    by (meson big_iff_small_termination final_def rtranclp.rtrancl_refl small1_big_continue)
  from 0 1 show "\<exists> t. (c,s) \<Rightarrow>\<^sub>g t" by(simp add: terminating_induct[of "(c,s)" "\<lambda> x.\<exists> t. x \<Rightarrow>\<^sub>g t"])
qed

section \<open>Termination equations\<close>

text \<open> 
 We state now under what conditions are the different constructs terminating. 
 These proofs are of special relevance while deriving the weakest post-conditions
 as wp are defined in terms of termination of the command and the wlp. 
\<close>

lemma skip_terminates: "terminating (SKIP,s)"
  by (meson final_def final_iff_SKIP terminating.intros)

lemma assign_terminates: "terminating (x1 ::= x2, s)"
  by (metis sAssignE skip_terminates terminating.intros)
 
lemma skip_seq_terminates: "terminating (SKIP;;c,s) \<longleftrightarrow> terminating (c,s)"
  apply(rule iffI)
  using terminating.simps apply blast
  by (metis final_def final_iff_SKIP sSeqE terminating.intros)

text \<open>
 A terminology introduced in Dijkstra's paper. BB holds when at least one of the
 guards is true (activated). If BB holds, IF is non-blocking and if BB does not hold
 DO ends with SKIP. 
\<close>

definition "BB gcs s \<equiv> \<exists> b c. (b,c) \<in> set gcs \<and> bval b s" 

lemma if_terminates: 
  "terminating (IF gcs FI,s) = 
  (BB gcs s \<and> (\<forall> b c. ((b,c) \<in> set gcs \<and> bval b s) \<longrightarrow> terminating (c,s)))"
  unfolding BB_def
  apply(rule iffI)
  apply (meson IfBlock_simp IfTrue must_imp_may terminating.simps)
  by (metis sIfBlockE terminating.simps)

(* Observation: (c,s) \<rightarrow>\<^sub>g (c',s') \<Longrightarrow> (c;;cc,s) \<rightarrow>\<^sub>g (c';;cc, s') *)
thm terminating.induct
lemma seq_termination_1:
  assumes "terminating (c1;;c2,s)"
  shows "terminating (c1,s)"
  using assms
proof (induction "(c1;;c2,s)" arbitrary: c1 s rule: terminating.induct)
  case 1 then show ?case
    using Seq2 terminating.intros by force
qed

lemma seq_termination_2: 
  "terminating (c1;;c2,s) \<Longrightarrow>
  (c1,s) \<Rightarrow>\<^sub>g t \<Longrightarrow>
  terminating (c2,t)"  
  apply(induction "(c1;;c2,s)" arbitrary: c1 s rule: terminating.induct)
  by (metis Pair_inject Seq1 Seq2 big_to_small converse_rtranclpE2 small_to_big)

lemma seq_termination_imp_1: "terminating (c1;;c2,s) \<Longrightarrow>
       terminating (c1,s) \<and> (\<forall> t. (c1,s) \<Rightarrow>\<^sub>g t \<longrightarrow> terminating (c2,t))"
  using seq_termination_1 seq_termination_2 by blast

lemma seq_terminating_3: "(c,s) \<Rightarrow>\<^sub>g t \<Longrightarrow> c = SKIP \<or> (\<exists> c' s'. (c,s) \<rightarrow>\<^sub>g (c',s') \<and> (c',s') \<Rightarrow>\<^sub>g t)"
  by(metis big_iff_small big_to_small converse_rtranclpE old.prod.exhaust snd_conv swap_simp)
  
lemma seq_termination_imp_2: 
  assumes "terminating (c1,s)"
  assumes "(\<forall> t. (c1,s) \<Rightarrow>\<^sub>g t \<longrightarrow> terminating (c2,t))"
  assumes "(\<exists> t. (c1,s) \<Rightarrow>\<^sub>g t \<and> terminating (c2,t))"
  shows "terminating (c1;;c2,s)"
  using assms
proof(induction "(c1,s)" arbitrary: c1 c2 s  rule: terminating.induct)
  case 1
  then have "\<forall> c1' s'. (c1, s) \<rightarrow>\<^sub>g (c1', s') \<longrightarrow> terminating (c1';; c2, s')" 
    by (meson must_imp_may small1_big_continue)
  moreover have "\<exists> c1' s'. (c1, s) \<rightarrow>\<^sub>g (c1', s') \<or> c1 = SKIP" 
    using "1" seq_terminating_3 by blast
  moreover have "c1 = SKIP \<Longrightarrow> terminating (c1;; c2, s)" 
    using "1.prems"(2) skip_seq_terminates by auto
  ultimately show ?case by (metis sSeqE terminating.simps)
qed

theorem seq_termination:
  "terminating (c1;;c2,s) \<longleftrightarrow>
    terminating (c1,s) \<and> 
    (\<forall> t. (c1,s) \<Rightarrow>\<^sub>g t \<longrightarrow> terminating (c2,t)) \<and>
    (\<exists> t. (c1,s) \<Rightarrow>\<^sub>g t \<and> terminating (c2,t))"
  by (meson must_imp_may seq_termination_imp_1 seq_termination_imp_2)

text \<open> 
 In contrast with the above, we have not found/needed a full characterization 
 of DO termination.
\<close>

lemma do_termination_1:
  "\<not> BB gcs s \<Longrightarrow> terminating (DO gcs OD,s)" 
  by (metis BB_def sDoWhileE skip_terminates terminating.intros)

lemma do_termination_2: 
  assumes "terminating (DO gcs OD,s)"
  assumes "BB gcs s"
  shows "terminating (IF gcs FI,s)"
  using assms
  by (meson gsmall_step.DoTrue if_terminates seq_termination_1 terminating.cases)

section \<open>A terminating computation leads to a finite number of states\<close>

text \<open>
 We continue here the theory that we started in the last section of the small-step
 semantics. The goal is to prove that the set of final states in the big-step semantics
 is finite, when the command is assumed to be terminating. This will be used in one
 of the weakest precondition proofs.
\<close>

lemma one_step_star: "{cs'. cs \<rightarrow>\<^sub>g* cs'} \<subseteq>
       (\<Union> cs'\<in>(successors cs) . {cs''. cs' \<rightarrow>\<^sub>g* cs''}) \<union> {cs} " (is "?A \<subseteq> ?B")
proof
   fix cs'
   assume "cs' \<in> ?A"
   then have "cs \<rightarrow>\<^sub>g* cs'" by simp
   then have "(\<exists> cs''. cs \<rightarrow>\<^sub>g cs'' \<and> cs'' \<rightarrow>\<^sub>g* cs') \<or> (cs' = cs)" 
     using converse_rtranclpE by fastforce
   then show "cs' \<in> ?B" using successors_def by blast   
 qed

lemma end_imp_finite_closure: "
 terminating (c,s) \<Longrightarrow> finite {(c',s').(c,s) \<rightarrow>\<^sub>g* (c',s')}
"
proof(induction "(c,s)" arbitrary: c s rule: terminating.induct)
  case 1
  have "(\<forall> cs' \<in> successors (c,s). finite {cs''. cs' \<rightarrow>\<^sub>g* cs''})" 
    using "1.hyps"(2) successors_def by auto
  then have 0: "finite ((\<Union> cs'\<in>(successors (c,s)) . {cs''. cs' \<rightarrow>\<^sub>g* cs''}) \<union> {(c,s)})"
    by (simp add: finite_succs)
  have "{(c', s'). (c, s) \<rightarrow>\<^sub>g* (c', s')} \<subseteq> 
         ((\<Union> cs'\<in>(successors (c,s)) . {cs''. cs' \<rightarrow>\<^sub>g* cs''}) \<union> {(c,s)})" 
    using one_step_star by auto
  then show ?case using "0" infinite_super by blast
qed

theorem finite_terminating: "terminating (c,s) \<Longrightarrow> finite {t.(c,s) \<Rightarrow>\<^sub>g t}"
proof -
  assume 0: "terminating (c,s)"
  have "{(c',s').(c,s) \<rightarrow>\<^sub>g* (c',s') \<and> c' = SKIP} \<subseteq> 
        {(c',s').(c,s) \<rightarrow>\<^sub>g* (c',s')}" 
    by (simp add: Collect_mono_iff)
  then have 1: "finite {(c',s').(c,s) \<rightarrow>\<^sub>g* (c',s') \<and> c' = SKIP}" 
    using "0" end_imp_finite_closure infinite_super by blast
  then have 2: "finite (snd `{(c',s').(c,s) \<rightarrow>\<^sub>g* (SKIP,s') \<and> c' = SKIP})" 
    by (smt Collect_cong finite_imageI prod.case_eq_if)
  have 3: "{s'.(c,s) \<rightarrow>\<^sub>g* (SKIP,s')} \<subseteq> snd `{(c',s').(c,s) \<rightarrow>\<^sub>g* (SKIP,s') \<and> c' = SKIP} "
    using image_iff by fastforce
  from "2" "3" have 4: "finite {s'.(c,s) \<rightarrow>\<^sub>g* (SKIP,s')}" 
    using infinite_super by auto
  have 5: "{t.(c,s) \<Rightarrow>\<^sub>g t} \<subseteq> {s'.(c,s) \<rightarrow>\<^sub>g* (SKIP,s')}" 
  proof 
    fix t 
    assume "t \<in> {t.(c,s) \<Rightarrow>\<^sub>g t}" 
    then have "(c,s) \<Rightarrow>\<^sub>g t" by blast
    then have "(c,s) \<rightarrow>\<^sub>g* (SKIP,t)" using big_to_small by auto
    then show "t \<in> {s'.(c,s) \<rightarrow>\<^sub>g* (SKIP,s')}" using image_iff by fastforce
  qed
  from "4" "5" show ?thesis using infinite_super by auto
qed


end