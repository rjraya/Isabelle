section \<open>Introduction to IMP2-VCG\<close>
theory Introduction
imports "vcg/VCG"
begin

  subsection \<open>Adding more Operators\<close>

  value "bval (Cmpop (\<le>) (Binop (+) (Unop uminus (V ''x'')) (N 42)) (N 50)) <''x'':=-5> "
    
  thm aval.simps bval.simps
  


  subsection \<open>Program Syntax\<close>

  definition "exp_count_up1 \<equiv> 
    ''a'' ::= N 1;;
    ''c'' ::= N 0;;
    WHILE Cmpop (<) (V ''c'') (V ''n'') DO (
      ''a'' ::= Binop ( * ) (N 2) (V ''a'');; 
      ''c'' ::= Binop (+) (V ''c'') (N 1))"

  (* Type \ < ^ imp > \open \close , without the spaces.
  
    for \<open>\<dots>\<close>, there is an autocompletion if you type a quote (")
    
    for \<comment> \<open>\<close>, type \comment and use autocompletion
    
  *)
  definition "exp_count_up2 \<equiv> \<^imp>\<open>
    \<comment> \<open>Initialization\<close>
    a = 1;
    c = 0;
    while (c<n) { \<comment> \<open>Iterate until \<open>c\<close> has reached \<open>n\<close>\<close>
      a=2*a; \<comment> \<open>Double \<open>a\<close>\<close>
      c=c+1  \<comment> \<open>Increment \<open>c\<close>\<close>
    }
  \<close>"    
      
  lemma "exp_count_up1 = exp_count_up2"
    unfolding exp_count_up1_def exp_count_up2_def ..
  

  subsection \<open>More Readable VCs\<close>
  lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib
  
  lemma "s\<^sub>0 ''n'' \<ge> 0 \<Longrightarrow> wlp exp_count_up1 (\<lambda>s. s ''a'' = 2^nat (s\<^sub>0 ''n'')) s\<^sub>0"
    unfolding exp_count_up1_def
    apply (subst annotate_whileI[where 
          I="\<lambda>s. s ''n'' = s\<^sub>0 ''n'' \<and>  s ''a'' = 2 ^ nat (s ''c'') \<and> 0 \<le> s ''c'' \<and> s ''c'' \<le> s\<^sub>0 ''n''" 
        ])
    apply i_vcg_generate
    subgoal for s
      thm VBINDI
      thm VBINDI[of s "''n''"]
      apply (rule VBINDI[of s "''n''"], rename_tac n)
      apply (rule VBINDI[of s\<^sub>0 "''n''"], rename_tac n\<^sub>0)
      apply (rule VBINDI[of s "''a''"], rename_tac a)
      apply (rule VBINDI[of s "''c''"], rename_tac c)
      apply (simp only: VBINDD)
      apply (thin_tac "VBIND _ _ _")+
    
      apply (auto simp: algebra_simps nat_distribs)
      done
    done
  

  lemma "s\<^sub>0 ''n'' \<ge> 0 \<Longrightarrow> wlp exp_count_up1 (\<lambda>s. s ''a'' = 2^nat (s\<^sub>0 ''n'')) s\<^sub>0"
    unfolding exp_count_up1_def
    apply (subst annotate_whileI[where 
          I="\<lambda>s. s ''n'' = s\<^sub>0 ''n'' \<and>  s ''a'' = 2 ^ nat (s ''c'') \<and> 0 \<le> s ''c'' \<and> s ''c'' \<le> s\<^sub>0 ''n''" 
        ])
    apply i_vcg_generate
    apply i_vcg_postprocess_vars
    apply (auto simp: algebra_simps nat_distribs)
    done
    

  subsection \<open>More Readable Annotations\<close>    
    
  
  
  lemma "let n = s\<^sub>0 ''n'' in n \<ge> 0 
    \<Longrightarrow> wlp exp_count_up1 (\<lambda>s. let a = s ''a''; n\<^sub>0 = s\<^sub>0 ''n'' in a = 2^nat (n\<^sub>0)) s\<^sub>0"
    unfolding exp_count_up1_def
    apply (subst annotate_whileI[where 
          I="\<lambda>s. s ''n'' = s\<^sub>0 ''n'' \<and>  s ''a'' = 2 ^ nat (s ''c'') \<and> 0 \<le> s ''c'' \<and> s ''c'' \<le> s\<^sub>0 ''n''" 
          (* Similar for invar! *)
        ])
    apply i_vcg_generate
    apply i_vcg_postprocess_vars
    apply (auto simp: algebra_simps nat_distribs)
    done
  
  lemma "VAR s x P = (let v=s x in P v)" unfolding VAR_def by simp 
    
  program_spec (partial) exp_count_up
    assumes "0\<le>n"               \<comment> \<open>Precondition. Use variable names of program.\<close>
    ensures "a = 2^nat n\<^sub>0"       \<comment> \<open>Postcondition. Use variable names of programs. 
                                      Suffix with \<open>\<cdot>\<^sub>0\<close> to refer to initial state\<close>
    defines                     \<comment> \<open>Program\<close>
    \<open>
      a = 1;
      c = 0;
      while (c<n) 
        @invariant \<open>n=n\<^sub>0 \<and> a=2^nat c \<and> 0\<le>c \<and> c\<le>n\<close> \<comment> \<open>
            Invar annotation. Variable names and suffix \<open>\<cdot>\<^sub>0\<close> for variables from initial state.\<close>
      {
        a=2*a;
        c=c+1
      }
    \<close>
    apply vcg
    by (auto simp: algebra_simps nat_distribs)

  thm exp_count_up_spec  
  thm exp_count_up_def
      
  
          
          
        

end
