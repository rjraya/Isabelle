theory tut10
  imports "IMP2.VCG" "IMP2.Examples"
          
begin


theorem 
  assumes "\<forall> a \<in> dom \<pi>. \<pi> a = \<pi>' a"
  assumes "\<pi>:(c,s) \<Rightarrow> t"
  shows "\<pi>':(c,s) \<Rightarrow> t"
  using assms big_step_mono_prog map_le_def by blast

(* slow way *)

theorem 
  assumes "\<forall> a \<in> dom \<pi>. \<pi> a = \<pi>' a"
  assumes "\<pi>:(c,s) \<Rightarrow> t"
  shows "\<pi>':(c,s) \<Rightarrow> t"
  using assms(2,1)
  apply (induction \<pi> c s t rule: big_step_induct)
  apply auto
  by (metis PCall domI)
 
procedure_spec pop (stack,ptr) returns (x,stack,ptr)
  assumes "ptr > 0"
  ensures "ptr = ptr\<^sub>0 - 1 \<and> ptr \<ge> 0 \<and> x = stack ptr \<and> stack ` {0..<ptr} = stack\<^sub>0 ` {0..<ptr}"
defines
\<open>ptr = ptr - 1; x = stack[ptr]\<close>
  by vcg_cs

procedure_spec push (x,stack,ptr) returns (stack,ptr)
  assumes "ptr \<ge> 0"
  ensures "ptr = ptr\<^sub>0 + 1 \<and> ptr > 0 \<and> stack ` {0..<ptr} = stack ` {0..<ptr\<^sub>0} \<union> {x\<^sub>0}"
  for x
defines 
\<open>stack[ptr] = x; ptr = ptr + 1 \<close>
  by vcg_cs fastforce
  
procedure_spec (partial) dfs
  assumes "0 \<le> x \<and> 0 \<le> s"
  ensures "b = 1 \<longrightarrow> x \<in> (Edges a)\<^sup>* `` {s}" defines \<open>
  b = 0;
  clear stack[];
  (stack,i) = push(s,stack,i);
  while (b == 0 \<and> i \<noteq> 0)
    @invariant \<open>0 \<le> i \<and> 
    stack ` {0..<(if b = 1 then i + 1 else i)} \<subseteq> (Edges a)\<^sup>* `` {s}
    \<and> (b = 1 \<longrightarrow> stack i = x)\<close>
  {
    (next,stack,i) = pop(stack,i);
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