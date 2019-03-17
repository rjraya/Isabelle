theory Check
  imports Submission
begin

theorem euclid_extended_spec:
 "HT_mods {''t'', ''r'', ''s'', ''temp'', ''old_t'', ''old_r'', ''old_s'', ''quotient''}
  (\<lambda>\<ss>. VAR (\<ss> ''b'' 0) (\<lambda>b. VAR (\<ss> ''a'' 0) (\<lambda>a. BB_PROTECT (0 < a \<and> 0 < b)))) euclid_extended
  (\<lambda>\<ss>\<^sub>0 \<ss>.
      VAR (\<ss>\<^sub>0 ''b'' 0)
       (\<lambda>b\<^sub>0. VAR (\<ss>\<^sub>0 ''a'' 0)
               (\<lambda>a\<^sub>0. VAR (\<ss> ''old_t'' 0)
                       (\<lambda>old_t.
                           VAR (\<ss> ''old_s'' 0)
                            (\<lambda>old_s.
                                VAR (\<ss> ''old_r'' 0)
                                 (\<lambda>old_r.
                                     BB_PROTECT
                                      (old_r = gcd a\<^sub>0 b\<^sub>0 \<and> gcd a\<^sub>0 b\<^sub>0 = a\<^sub>0 * old_s + b\<^sub>0 * old_t)))))))"
  by (rule Submission.euclid_extended_spec)

theorem equilibrium_spec:
 "HT_mods {''i'', ''lsum'', ''usum''} (\<lambda>\<ss>. VAR (\<ss> ''l'' 0) (\<lambda>l. VAR (\<ss> ''h'' 0) (\<lambda>s. BB_PROTECT (l \<le> s))))
  equilibrium
  (\<lambda>\<ss>\<^sub>0 \<ss>.
      VAR (\<ss> ''l'' 0)
       (\<lambda>l. VAR (\<ss> ''i'' 0)
             (\<lambda>i. VAR (\<ss> ''h'' 0)
                   (\<lambda>h. VAR (\<ss> ''a'') (\<lambda>a. BB_PROTECT (is_equil a l h i \<or> i = h \<and> \<not> Ex (is_equil a l h)))))))
"
  by (rule Submission.equilibrium_spec)

end