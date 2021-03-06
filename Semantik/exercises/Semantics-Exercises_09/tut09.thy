theory tut09
  imports
   "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP2/automation/IMP2_VCG"
   "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP2/doc/Examples"          
begin

lemma [named_ss vcg_bb]:
  "lhsv (Inline c) = lhsv c"
  unfolding Inline_def ..

definition succs where
  "succs a i \<equiv> a ` {i+1..<a i}" for a :: "int \<Rightarrow> int"

definition Edges where
  "Edges a \<equiv> {(i, j). j \<in> succs a i}"

program_spec get_succs'
  assumes "j \<le> stop"
  ensures "stack ` {0..<i\<^sub>0} = stack\<^sub>0 ` {0..<i\<^sub>0}
    \<and> lran stack i\<^sub>0 i = filter (\<lambda> x. x \<notin> set_of visited) (lran a j\<^sub>0 stop)
    \<and> i \<ge> i\<^sub>0"
defines
\<open>
  while (j < stop)
  @invariant \<open>stack ` {0..<i\<^sub>0} = stack\<^sub>0 ` {0..<i\<^sub>0}
    \<and> lran stack i\<^sub>0 i = filter (\<lambda> x. x \<notin> set_of visited) (lran a j\<^sub>0 j) \<and> j \<le> stop \<and> i\<^sub>0 \<le> i \<and> j\<^sub>0 \<le> j
  \<close>
  @variant \<open>stop - j\<close>
  {
    succ = a[j];
    if (visited[succ] == 0) {
      stack[i] = succ;
      i = i + 1
    };
    j = j + 1
  }
\<close>
  apply vcg_cs
  apply auto
  by (metis atLeastLessThan_iff image_iff lran_upd_outside(2) set_lran)

program_spec get_succs
  assumes "j \<le> stop \<and> stop = a (j - 1)"
  ensures "stack ` {0..<i\<^sub>0} = stack\<^sub>0 ` {0..<i\<^sub>0}
    \<and> set (lran stack i\<^sub>0 i) = {x. (j\<^sub>0 - 1, x) \<in> Edges a \<and> x \<notin> set_of visited} \<and> i \<ge> i\<^sub>0"
  for i j stop stack[] a[] visited[]
defines \<open>inline get_succs'\<close>
  by vcg_cs (auto simp: Edges_def succs_def set_lran)

program_spec get_succs1
  assumes "j \<le> stop \<and> stop = a (j - 1) \<and> 0 \<le> i"
  ensures "
    stack ` {0..<i} = {x. (j\<^sub>0 - 1, x) \<in> Edges a \<and> x \<notin> set_of visited} \<union> stack\<^sub>0 ` {0..<i\<^sub>0}
    \<and> i \<ge> i\<^sub>0"
  for i j stop stack[] a[] visited[]
defines
\<open>inline get_succs\<close>
  apply vcg_cs
  unfolding set_lran
  by (metis (no_types, lifting) Un_commute image_Un ivl_disj_un_two(3))

program_spec (partial) dfs
  assumes "0 \<le> x \<and> 0 \<le> s"
  ensures "b = 1 \<longrightarrow> x \<in> (Edges a)\<^sup>* `` {s}" defines \<open>
  b = 0;
  i = 1;
  stack[0] = s;
  while (b == 0 \<and> i \<noteq> 0)
    @invariant \<open>0 \<le> i \<and> 
    stack ` {0..<(if b = 1 then i + 1 else i)} \<subseteq> (Edges a)\<^sup>* `` {s}
    \<and> (b = 1 \<longrightarrow> stack i = x)\<close>
  {
    i = i - 1;
    next = stack[i]; \<comment>\<open>Take the top most element from the stack.\<close>
    if (next == x) {
      b = 1 \<comment>\<open>If it is the target, we are done.\<close>
    } else {
      visited[next] = 1; \<comment>\<open>Else, mark it as visited,\<close>
      \<comment>\<open>and put its successors on the stack if they are not yet visited.\<close>
      stop = a[next];
      j = next + 1;
      if (j \<le> stop) {
        inline get_succs1
      }
    }
  }
\<close>
  apply vcg_cs
  subgoal for s\<^sub>0 x\<^sub>0 sb i a x stack visited
    apply safe
     apply (rule rtrancl.rtrancl_into_rtrancl[rotated])
    by (simp add: image_subset_iff)+
  subgoal for s\<^sub>0 x\<^sub>0 sa i a x
    by (simp add: image_subset_iff)
  by (simp add: image_subset_iff)

end