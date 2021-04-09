theory Check
  imports Submission
begin

theorem array_assign: "(x[] ::= a;; a[] ::= x) \<sim> (x[] ::= a)"
  by (rule Submission.array_assign)

theorem partition_spec:
 "HT_mods {''j'', ''a'', ''i'', ''temp''} (\<lambda>\<ss>. VAR (\<ss> ''l'' 0) (\<lambda>l. VAR (\<ss> ''h'' 0) (\<lambda>s. BB_PROTECT (l \<le> s)))) partition
  (\<lambda>\<ss>\<^sub>0 \<ss>.
      VAR (\<ss>\<^sub>0 ''l'' 0)
       (\<lambda>l\<^sub>0. VAR (\<ss>\<^sub>0 ''h'' 0)
               (\<lambda>h\<^sub>0. VAR (\<ss>\<^sub>0 ''a'')
                       (\<lambda>a\<^sub>0. VAR (\<ss> ''i'' 0)
                               (\<lambda>i. VAR (\<ss> ''a'')
                                     (\<lambda>a. BB_PROTECT
                                           (mset_ran a {l\<^sub>0..<i} = filter_mset ((\<le>) 0) (mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0}) \<and>
                                            mset_ran a {i..<h\<^sub>0} = {#x \<in># mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0}. x < 0#})))))))"
  by (rule Submission.partition_spec)

end