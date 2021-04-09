lemma impa1: "(x[] ::= a;; a[] ::= x,s) \<Rightarrow> t \<Longrightarrow> (x[] ::= a,s) \<Rightarrow> t"
  by (smt ArrayCpyE SeqE fun_upd_same fun_upd_triv fun_upd_twist)

lemma impa2: "(x[] ::= a,s) \<Rightarrow> t \<Longrightarrow> (x[] ::= a;; a[] ::= x,s) \<Rightarrow> t"
  by (smt ArrayCpy ArrayCpyE Seq fun_upd_def fun_upd_idem_iff)

theorem array_assign: "(x[] ::= a;; a[] ::= x) \<sim> (x[] ::= a)"
  by (simp add: Semantics.equivI impa1 impa2)

lemma impb1: "(x[i] ::= Vidx a j, s) \<Rightarrow> s' \<Longrightarrow>
         aval i s = aval i s' \<Longrightarrow>
         aval j s = aval j s' \<Longrightarrow>
         (x[i] ::= Vidx a j;; a[j] ::= Vidx x i, s) \<Rightarrow> t \<Longrightarrow> 
              (x[i] ::= Vidx a j, s) \<Rightarrow> t"
  by (smt AssignIdxE SeqE aval.simps(2) fun_upd_idem fun_upd_other fun_upd_same) 

lemma impb2: "(x[i] ::= Vidx a j, s) \<Rightarrow> s' \<Longrightarrow>
         aval i s = aval i s' \<Longrightarrow>
         aval j s = aval j s' \<Longrightarrow>
         (x[i] ::= Vidx a j, s) \<Rightarrow> t \<Longrightarrow> 
              (x[i] ::= Vidx a j;; a[j] ::= Vidx x i, s) \<Rightarrow> t"
  by (smt Assign' AssignIdxE Seq aval.simps(2) fun_upd_apply fun_upd_idem_iff)

theorem
  "(\<forall> s s' .(x[i] ::= Vidx a j, s) \<Rightarrow> s' \<longrightarrow>
         aval i s = aval i s' \<and>
         aval j s = aval j s') \<Longrightarrow>
   (x[i] ::= Vidx a j;; a[j] ::= Vidx x i) \<sim> (x[i] ::= Vidx a j)"
  by (meson Assign' equiv_c_def impb1 impb2)


program_spec array_filter
  assumes "l\<le>h"
  ensures "l \<le> bi \<and> bi \<le> h \<and> 
           l \<le> ci \<and> ci \<le> h \<and>
           (ci - l + bi - l = h - l) \<and>
           lran b l\<^sub>0 bi = filter (\<lambda>x. x\<ge>0) (lran a\<^sub>0 l\<^sub>0 h\<^sub>0) \<and>
           lran c l\<^sub>0 ci = filter (\<lambda>x. x<0) (lran a\<^sub>0 l\<^sub>0 h\<^sub>0)"
  defines \<open>
    bi=l; j=l; ci=l; 
    while (j<h) 
      @invariant \<open> 
          l\<le>bi \<and> bi\<le>j \<and> j\<le>h     
        \<and> l\<le>ci \<and> ci\<le>j \<and> j\<le>h 
        \<and> ci - l + bi - l = j - l
        \<and> lran b l bi = filter (\<lambda>x. x \<ge> 0) (lran a\<^sub>0 l j)
        \<and> lran c l ci = filter (\<lambda>x. x<0) (lran a\<^sub>0 l j)
        \<and> lran b j h = lran b\<^sub>0 j h
      \<close>
      @variant \<open>nat (h-j)\<close>
    {
      if (a[j]\<ge>0) {b[bi] = a[j]; bi=bi+1}
      else {c[ci] = a[j]; ci=ci+1};
      j=j+1
    }
  \<close>
  supply lran_eq_iff[simp] lran_tail[simp del]
  apply vcg_cs
  done

program_spec append_sorted
  assumes "l \<le> bi \<and> bi \<le> (ci+bi-l) \<and> 
           l \<le> ci \<and> ci \<le>(ci+bi-l)"
  ensures "(lran a l bi = lran b l bi) \<and>
           (lran a bi (ci+bi-l) = lran c l ci)"
defines
\<open>
t = l;
while(t < bi)
 @invariant \<open>l \<le> t \<and> t \<le> bi \<and>
             (lran a l t = lran b l t)\<close>
 @variant \<open>nat (bi-t)\<close>
{
 a[t] = b[t];
 t = t+1
};

t = l;
while(t < ci)
 @invariant \<open>l \<le> t \<and> t \<le> ci \<and> 
             (lran a l bi = lran b l bi) \<and>
             (lran a bi (t+bi-l) = lran c l t)\<close>
 @variant \<open>nat (ci-t)\<close>
{
 a[t+bi-l] = c[t];
 t = t+1
}
\<close>          
  apply vcg_cs
  by (smt fun_upd_same lran_bwd_simp lran_upd_outside(2))

  
program_spec partition
  assumes "l\<le>h"
  ensures "mset_ran a {l\<^sub>0..<i} = filter_mset (\<lambda>x. x \<ge> 0) (mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0})
         \<and> mset_ran a {i..<h\<^sub>0} = filter_mset (\<lambda>x. x < 0) (mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0})"
defines
\<open>
a[] = a; 
i = 0;
j = l; 
i = h; 
temp = i;
inline array_filter;
inline append_sorted;
i = bi
\<close>
  apply vcg_cs
  by (metis mset_filter mset_lran)