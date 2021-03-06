theory Small_step
  imports "Main" Syntax Big_step
begin

section \<open>Semantic definition of the GCL language.\<close>

text \<open>
 Our first approach was as follows:

 \<open>\<Rightarrow>\<^sub>g\<close> would no longer reflect accurately the terminating behaviour of \<open>\<rightarrow>\<^sub>g\<close>. 
  In particular, there would be two kind of terminating behaviours for \<open>\<rightarrow>\<^sub>g\<close>:
  
  - abortion: here \<open>\<rightarrow>\<^sub>g\<close> would terminate but \<open>\<Rightarrow>\<^sub>g\<close> would not yield a final state. 
              this would happen when we get a blocking if as the first command.
  - termination: here \<open>\<rightarrow>\<^sub>g\<close> would terminate and \<open>\<Rightarrow>\<^sub>g\<close> would yield a final state. 
                 this would happen when we get SKIP as the last command.

  The proof went by defining a function first_command that would take care of finding
  the first command of a possibly nested sequential command. Then we performed induction
  based on this function.

  However, this approach was removed because it would complicate the notion of weakest
  precondition. Indeed, Dijkstra states that we shall use the notation wp(S, R) for:
   
  the weakest precondition for the initial state of the system such that
  activation of S is guaranteed to lead to a PROPERLY terminating activity ...
 
  that is, we should exclude abortion from the terminating relation. With this semantics
  the abortion situations lead to self infinite loops.
\<close>

subsection \<open>Small-step semantics definition\<close>

inductive gsmall_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>g" 55)
where
 Assign:  "(x ::= a, s) \<rightarrow>\<^sub>g (SKIP, s(x := aval a s))" |
 Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow>\<^sub>g (c\<^sub>2,s)" |
 Seq2:    "(c\<^sub>1,s) \<rightarrow>\<^sub>g (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow>\<^sub>g (c\<^sub>1';;c\<^sub>2,s')" |
 IfFalse: "(\<forall> b c. (b,c) \<in> set gcs \<longrightarrow> \<not> bval b s) \<Longrightarrow> (IF gcs FI,s) \<rightarrow>\<^sub>g (IF gcs FI,s)" |
 IfTrue: "(b,c) \<in> set gcs \<Longrightarrow> bval b s \<Longrightarrow> (IF gcs FI,s) \<rightarrow>\<^sub>g (c,s)" |
 DoTrue:  "(b,c) \<in> set gcs \<Longrightarrow> bval b s \<Longrightarrow> (DO gcs OD,s) \<rightarrow>\<^sub>g (c;;DO gcs OD,s)" |
 DoFalse: "(\<forall> b c. (b,c) \<in> set gcs \<longrightarrow> \<not> bval b s) \<Longrightarrow> (DO gcs OD,s) \<rightarrow>\<^sub>g (SKIP,s)"

abbreviation small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>g*" 55)
  where "x \<rightarrow>\<^sub>g* y \<equiv> (gsmall_step\<^sup>*\<^sup>* x y)"

abbreviation small_1_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>g+" 55)
  where "x \<rightarrow>\<^sub>g+ y \<equiv> (gsmall_step\<^sup>+\<^sup>+ x y)"

subsection \<open>Proof automation.\<close>

lemmas gsmall_step_induct = gsmall_step.induct[split_format(complete)]
declare gsmall_step.intros[simp,intro]

inductive_cases sAssignE[elim!]: "(x ::= a, s) \<rightarrow>\<^sub>g t"
inductive_cases sSeqE[elim!]: "(c1 ;; c2, s) \<rightarrow>\<^sub>g t"
inductive_cases sIfBlockE[elim!]: "(IF gs FI, s) \<rightarrow>\<^sub>g t"
inductive_cases sDoWhileE[elim]: "(DO gcs OD, s) \<rightarrow>\<^sub>g t"

lemmas star_induct = converse_rtranclp_induct2 (* Pairs *)
lemmas star_induct1 = converse_rtranclp_induct (* No pairs *)

section \<open>Relation to big-step semantics\<close>

text \<open> 
 With the small-step semantics that we have chosen the proofs here are completely
 analogous to the ones seen in class for IMP.
\<close>

lemma star_seq2: "(c1,s) \<rightarrow>\<^sub>g* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>\<^sub>g* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case (step c1 s1 ch sh)
  from Seq2[OF step.hyps(1)] have "(c1;; c2, s1) \<rightarrow>\<^sub>g (ch;; c2, sh)" .
  also have \<open>\<dots> \<rightarrow>\<^sub>g* (c1';; c2, s')\<close> by (rule step.IH)
  finally show ?case .
qed

lemma big_to_small: "cs \<Rightarrow>\<^sub>g t \<Longrightarrow> cs \<rightarrow>\<^sub>g* (SKIP,t)"
  apply(induction rule: gbig_step.induct)
  apply simp
  apply blast
  apply (meson Seq1 converse_rtranclp_into_rtranclp star_seq2 transitive_closurep_trans'(2))
  apply (meson IfTrue converse_rtranclp_into_rtranclp)
  apply (meson Seq1 converse_rtranclp_into_rtranclp DoTrue star_seq2 transitive_closurep_trans'(2))
  by blast
  
lemma small1_big_continue: "cs \<rightarrow>\<^sub>g cs' \<Longrightarrow> cs' \<Rightarrow>\<^sub>g t \<Longrightarrow> cs \<Rightarrow>\<^sub>g t"
 apply (induction arbitrary: t rule: gsmall_step.induct)
 apply auto
done

 lemma small_to_big: "cs \<rightarrow>\<^sub>g* (SKIP,t) \<Longrightarrow> cs \<Rightarrow>\<^sub>g t"
  apply (induction cs rule: star_induct1)
  apply (auto intro: small1_big_continue)
done

theorem big_iff_small: "cs \<Rightarrow>\<^sub>g t \<longleftrightarrow> cs \<rightarrow>\<^sub>g* (SKIP,t)" 
  by(metis big_to_small small_to_big)

section \<open>Final configurations and non-determinism\<close>

text \<open>
 Again the choice of the semantics proves useful to characterize what states are final.
 As in the case of IMP, only SKIP-configurations will be final.
\<close>

definition "final cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow>\<^sub>g cs')"

lemma skip_final: "c = SKIP \<Longrightarrow> final (c,s)" 
  using final_def gsmall_step.cases by fast

lemma final_commands:
  "final (c,s) \<Longrightarrow> (c = SKIP) "
  unfolding final_def 
  by(induction c,simp,blast,fast,blast+)

lemma final_iff_SKIP:
  "final (c,s) = (c = SKIP)"
  apply(rule iffI)
  using final_commands apply blast
  by (simp add: skip_final)

text \<open>
 The characterization of final configurations let us rewrite the relation between the
 small and the big step semantics in a more comprehensible way.
\<close>

lemma big_iff_small_termination: "(\<exists> t. cs \<Rightarrow>\<^sub>g t) = (\<exists> cs'. cs \<rightarrow>\<^sub>g* cs' \<and> final cs')"
  by (simp add: big_iff_small final_iff_SKIP)

text \<open>
 We give a counterexample, to prove that the small-step semantics is also non-deterministic.
 This again is a difference with the IMP language with important implications for the subsequent
 theories.
\<close>

lemma sdeterminism_counterexample:
  "gcs = [(Bc True,SKIP),(Bc True,s\<^sub>2 ::= (N 1) ;; SKIP)] \<Longrightarrow>
   c = IF gcs FI \<Longrightarrow>
   s = (\<lambda>x. 0)(s\<^sub>1 := 0, s\<^sub>2 := 0, s\<^sub>3 := 0) \<Longrightarrow>
   (SKIP,s) \<noteq> (s\<^sub>2 ::= (N 1) ;; SKIP,s) \<and> (c,s) \<rightarrow>\<^sub>g (SKIP,s) \<and> (c,s) \<rightarrow>\<^sub>g (s\<^sub>2 ::= (N 1) ;; SKIP,s)
  "
  for s :: "string \<Rightarrow> int"
  by simp

lemma snon_determinism: "\<not> (\<forall> cs cs' cs''. cs \<rightarrow>\<^sub>g cs' \<longrightarrow> cs \<rightarrow>\<^sub>g cs''  \<longrightarrow> cs' = cs'')"
  using sdeterminism_counterexample by blast
  

text \<open>
 As a consequence there is a difference between may terminate (there is a 
 terminating \<open>\<rightarrow>\<^sub>g\<close> path) and must terminate (all \<open>\<rightarrow>\<^sub>g\<close> paths terminate), since
 one path may terminate and another may not.

 Therefore, \<open>\<Rightarrow>\<^sub>g\<close> does not correctly reflect termination behaviour of \<open>\<rightarrow>\<^sub>g\<close>.  
\<close>

section \<open>The number of successors of \<open>\<rightarrow>\<^sub>g\<close> is finite\<close>

text \<open>
 We need this section in combination with some results in the termination theory,
 namely, the results stating that a terminating \<open>\<rightarrow>\<^sub>g\<close> ensures that the number of 
 leaves of the trees derivations are finite.

 This is needed while deriving the weakest precondition for the DO command as was
 stated in the paper by Dijkstra. It is however, an interesting result by itself.
 In particular, it made us work with properties related to finiteness of sets. 
\<close>

lemma skip_size: "{cs'.(SKIP,s) \<rightarrow>\<^sub>g cs'} = {}"
  using final_def skip_final by auto

lemma assign_size: "{cs'.(x ::= a,s) \<rightarrow>\<^sub>g cs'} = {(SKIP, s(x := aval a s))}" by blast

lemma finite_concat:
  "finite S \<and> (\<forall> x \<in> S'. \<exists> y \<in> S. x = f y) \<and> inj_on f S \<Longrightarrow> finite S'"
  by (metis finite_imageI finite_subset imageI subsetI)

lemma seq_size_1: "
 finite {cs'.(c1,s) \<rightarrow>\<^sub>g cs'} \<Longrightarrow>
 finite {cs'.(\<exists> c1' s'. cs' = (c1';;c2,s') \<and> (c1,s) \<rightarrow>\<^sub>g (c1',s'))}
" 
proof -
  let ?S = "{cs'.(c1,s) \<rightarrow>\<^sub>g cs'}"
  let ?S' = "{cs'.(\<exists> c1' s'. cs' = (c1';;c2,s') \<and> (c1,s) \<rightarrow>\<^sub>g (c1',s'))}"
  let ?f = "(\<lambda> cs'. (fst cs';;c2,snd cs'))"
  have 0: "inj_on ?f ?S" 
    by (meson Pair_inject com.inject(2) inj_onI prod_eq_iff)
  have 1: "(\<forall> x \<in> ?S'. \<exists> y \<in> ?S. x = ?f y)" by auto
  assume 2:"finite ?S"
  from "0" "1" "2" finite_concat[of ?S ?S' ?f] show "finite ?S'" by linarith
qed

lemma seq_size_2: "finite {cs'.(c1,s) \<rightarrow>\<^sub>g cs'} \<Longrightarrow> finite {cs'.(c1;;c2,s) \<rightarrow>\<^sub>g cs'}"
proof -
  have 0: "{cs'.(c1;;c2,s) \<rightarrow>\<^sub>g cs'} = 
       ({cs'.(\<exists> c1' s'. cs' = (c1';;c2,s') \<and> (c1,s) \<rightarrow>\<^sub>g (c1',s'))} \<union>
            {cs'.(c1 = SKIP \<and> cs' = (c2,s))})" by auto
  have 1: "finite {cs'.(c1 = SKIP \<and> cs' = (c2,s))}" by auto
  assume "finite {cs'.(c1,s) \<rightarrow>\<^sub>g cs'}"
  from this seq_size_1[of c1 s c2]
  have 2: "finite {(c1';; c2, s') |c1' s'. (c1, s) \<rightarrow>\<^sub>g (c1', s')}" by auto
  from "0" "1" "2" show ?thesis by simp
qed

lemma gcs_finite: "finite {cs'. \<exists> b c. cs' = (c,s) \<and> (b,c) \<in> set gcs}" 
proof -
  let ?f = "(\<lambda> gc. (snd gc,s))"
  have 0: "?f ` (set gcs) = {cs'. \<exists> b c. cs' = (c,s) \<and> (b,c) \<in> set gcs}" 
      by (smt Collect_cong Setcompr_eq_image prod.collapse snd_conv)
  have 1: "finite (set gcs)" by simp
  from "0" "1" show ?thesis by (metis finite_imageI)
qed

lemma if_size_1: "{cs'.(IF gcs FI,s) \<rightarrow>\<^sub>g cs'} \<subseteq> 
        {cs'. \<exists> b c. cs' = (c,s) \<and> (b,c) \<in> set gcs} \<union> {(IF gcs FI,s)}"
  by(induction gcs,blast+)

lemma if_size_2: "finite {cs'.(IF gcs FI,s) \<rightarrow>\<^sub>g cs'}" 
  using if_size_1[of gcs s] gcs_finite[of s gcs] 
  by (simp add: finite_subset)

lemma do_size_1: 
  "{cs'.(DO gcs OD,s) \<rightarrow>\<^sub>g cs'} \<subseteq>
     {cs'. \<exists> b c. cs' = (c;;DO gcs OD,s) \<and> (b,c) \<in> set gcs} \<union> {(SKIP,s)}" 
  by(induction gcs,blast+)

lemma gcs_finite_do: "finite {cs'. \<exists>b c. cs' = (c;; DO gcs OD, s) \<and> (b, c) \<in> set gcs}"
proof -
  let ?f = "(\<lambda> gc. (snd gc;; DO gcs OD,s))"
  have 0: "?f ` (set gcs) = {cs'. \<exists> b c. cs' = (c;; DO gcs OD,s) \<and> (b,c) \<in> set gcs}" 
    by (smt Collect_cong Setcompr_eq_image prod.collapse snd_conv)
  have 1: "finite (set gcs)" by simp
  from "0" "1" show ?thesis by (metis (no_types, lifting) finite_imageI)
qed

lemma do_size_2: "finite {cs'.(DO gcs OD,s) \<rightarrow>\<^sub>g cs'}" 
  using do_size_1[of gcs s] gcs_finite_do[of gcs s] 
  by (simp add: finite_subset)

lemma finite_step: "finite {cs'.(c,s) \<rightarrow>\<^sub>g cs'}"
  apply(induction c arbitrary: s)
  by(auto simp add: skip_size assign_size seq_size_2 if_size_2 do_size_2)

definition successors where
"successors cs = {cs'. cs \<rightarrow>\<^sub>g cs'}"

theorem finite_succs: "finite (successors cs)" 
  by (metis finite_step prod.exhaust_sel successors_def)

end