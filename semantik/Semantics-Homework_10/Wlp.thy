theory Wlp
  imports "Main" Syntax Big_step 
begin

section \<open>Weakest liberal precondition\<close>

text \<open>
 The definition of weakest liberal precondition stays the same as in IMP.
 The definition of weakest liberal precondition is not developed in "A Discipline
 of Programming", we provide some properties here for completeness, but we shall
 not use them in the future. 
\<close>

definition "wlp c Q s \<equiv> \<forall> t. (c,s) \<Rightarrow>\<^sub>g t \<longrightarrow> Q t"

subsection \<open>Basic properties\<close>

text\<open>
 Properties like the following are noted in Dijkstra's book 
 "A discipline of programming" (we include them for completeness)
\<close>

lemma included_miracle: "wlp c (\<lambda> t. True) = (\<lambda> t. True)" unfolding wlp_def by auto

text\<open>Weakest liberal precondition characterizes command equivalence\<close>

lemma wlp_equiv: "c \<sim>\<^sub>g c' \<longleftrightarrow> wlp c = wlp c'" 
  unfolding wlp_def equiv_gc_def 
  by (metis (no_types, hide_lams))

lemma wlp_conseq: "wlp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wlp c Q s" 
  unfolding wlp_def by auto

subsection \<open>Weakest liberal precondition equations\<close>
 
lemma wlp_skip_eq: "wlp SKIP Q s = Q s" unfolding wlp_def by auto
lemma wlp_assign_eq: "wlp (x::=a) Q s = Q (s(x:=aval a s))" unfolding wlp_def by auto
lemma wlp_seq_eq: "wlp (c\<^sub>1;;c\<^sub>2) Q s = wlp c\<^sub>1 (wlp c\<^sub>2 Q) s" unfolding wlp_def by auto

text \<open>
 One may want a mechanization of the following lemma that avoids quantification.
 Our first approach was:

 definition "and_fold l Q s = 
  fold (\<and>) (map (\<lambda> c. if bval (fst c) s then wlp (snd c) Q s else True) l) True"

 this may be reused if needed.
\<close>
lemma wlp_if_eq: "wlp (IF gcs FI) Q s = (\<forall> b c. ((b,c) \<in> set gcs \<and> bval b s) \<longrightarrow> wlp c Q s)"
  using wlp_def by auto

text \<open>
 Other ways of expressing the wlp for the do construct appear in:
 
 "Strongest Postcondition Semantics as the Formal Basis for Reverse Engineering"

 Lecture notes of Cornell university CS 6110 S11 Lecture 18 indicate that it is
 not expressible in first-order-logic and give an overaproximating proof rule instead.
\<close>

lemma wlp_do_eq: 
 "wlp (DO gcs OD) Q s = 
    ((\<forall> b c. ((b,c) \<in> set gcs \<and> bval b s) \<longrightarrow> wlp c (wlp (DO gcs OD) Q) s) \<and>
    ((\<forall> b c. ((b,c) \<in> set gcs) \<longrightarrow> \<not> bval b s) \<longrightarrow> Q s))"
  unfolding wlp_def 
  apply(rule iffI)
  using DoTrue apply fastforce
  by auto

end