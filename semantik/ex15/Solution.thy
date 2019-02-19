(*<*)
theory Solution
  imports "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP2/doc/Examples"

begin
(*>*)

text \<open>\ExerciseSheet{15}{05.~02.~2019}\<close>

text \<open>\Exercise{Program Verification} (Pen \& Paper)\<close>

paragraph \<open>Solution\<close>



program_spec check_anbn 
  assumes "0\<le>h"
  ensures "(i=j+1) \<longleftrightarrow> 
           ((\<forall> t. 0 \<le> t \<and> t < i \<longrightarrow> a t = 0) \<and>
            (\<forall> t. i \<le> t \<and> t < h \<longrightarrow> a t = 1) \<and>
            i = h - i)"
  defines \<open>
    i = 0;
    j = h - 1;
    while (i<j \<and> a[i] == 0 \<and> a[j] == 1) 
      @variant \<open>j-i+1\<close>
      @invariant \<open>
       (\<forall> t. 0 \<le> t \<and> t < i \<longrightarrow> a t = 0) \<and>
       (\<forall> t. j < t \<and> t < h \<longrightarrow> a t = 1) \<and>
       h - (j+1) = i \<and>
       (0 \<le> i \<and> i \<le> j \<and>  j \<le> h \<or> i = j+1)
        \<close>
    {
      i=i+1; 
      j=j-1
    }
  \<close>
  by (vcg_cs,smt,force)

 


text \<open>
  \Exercise{Hoare-Logic} (Pen \& Paper)
\<close>

text \<open>Solution:

  \<^enum> No. Consider \<open>t \<noteq> t'\<close>, and \<open>R = UNIV\<close>. Then \<open>(c,s) \<Rightarrow> t\<close> and \<open>(c,s) \<Rightarrow> t'\<close> for any \<open>s\<close>.
  \<^enum> \<open>wlp (REL R) Q s = (\<forall>t. (s, t) \<in> R \<longrightarrow> Q t)\<close>
  \<^enum>
    \<^descr>[Soundness] We first show \<open>(REL R, s) \<Rightarrow> t \<longleftrightarrow> (s, t) \<in> R\<close>. In the \<open>\<longrightarrow>\<close>-direction this follows
    by rule inversion on the big step, and in the \<open>\<longleftarrow>\<close>-direction we use rule \<open>Rel\<close>.
    Now \begin{align*}
      & & \<open>wlp (REL R) Q s\<close> \\
      & \<open>\<longleftrightarrow>\<close> & \<open>(\<forall>t. (REL R, s) \<Rightarrow> t \<longrightarrow> Q t)\<close> \\
      & \<open>\<longleftrightarrow>\<close> & \<open>(\<forall>t. (s, t) \<in> R \<longrightarrow> Q t)\<close>
    \end{align*}
    \<^descr>[Completeness] We need to show \<open>HT_partial (wlp c Q) (REL R) Q\<close>.
    \begin{align*}
      & & \<open>HT_partial (wlp c Q) (REL R) Q\<close> \\
      & \<open>\<longleftrightarrow>\<close> & \<open>(\<forall>s. wlp c Q s \<longrightarrow> wlp c Q s)\<close> \\
      & \<open>\<longleftrightarrow>\<close> & \<open>True\<close>
    \end{align*}
\<close>

(*<*)
end
(*>*)