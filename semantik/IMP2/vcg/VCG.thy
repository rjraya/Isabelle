section \<open>Verification Condition Generator\<close>
theory VCG
imports VCG_Specification VCG_Var_Postprocessor
begin

  subsubsection \<open>Generation of Verification Conditions\<close>
  (* TODO: Do we need the additional complexity of safe and unsafe unfolds? *)
  named_theorems vcg_rules \<open>Rules for VCG\<close>
  named_theorems vcg_safe_unfolds \<open>Unfold rules that can be applied without intermediate simp\<close>
  named_theorems vcg_unfolds \<open>Unfold rules to apply with intermediate simp\<close>
    
  
  method i_vcg_stepsimp = 
    (simp split del: if_split)? \<comment> \<open>Simplify subgoal\<close>

  method i_vcg_step_nosimp declares vcg_rules = 
      simp only: vcg_safe_unfolds
    | (subst vcg_unfolds | rule vcg_rules)
    
  method i_vcg_step declares vcg_rules = 
      simp only: vcg_safe_unfolds
    | (subst vcg_unfolds | rule vcg_rules); i_vcg_stepsimp?

  method i_vcg_generate declares vcg_rules = (i_vcg_step; i_vcg_generate)?
    \<comment> \<open>Recursively apply all possible steps\<close>
  
  subsection \<open>Preprocessing of Goal\<close>
  
  method i_vcg_preprocess = (unfold VAR_def ANNOTATION_def HT'_def HT'_partial_def)?; (intro allI impI conjI)?
  
  subsubsection \<open>VCG Main Interface\<close>  
  
  method vcg declares vcg_rules = i_vcg_preprocess; i_vcg_generate; i_vcg_postprocess_vars
    \<comment> \<open>Preprocess, generate VCs, and postprocess them\<close>
    
  method vcg_cs declares vcg_rules = vcg; clarsimp?
    \<comment> \<open>Generate VCs, postprocess and clarsimp them\<close>
  
  method vcg_auto declares vcg_rules = vcg; (auto;fail | clarsimp?)
    \<comment> \<open>Recursively apply all possible steps, try hard to solve VCs\<close>

  method vcg_force declares vcg_rules = vcg; (force | clarsimp?)
    \<comment> \<open>Recursively apply all possible steps, try even harder to solve VCs\<close>
    
  
  subsection \<open>VCG Setup for Wp and Wlp\<close>  

  lemmas [vcg_safe_unfolds] = wlp_seq_eq wlp_skip_eq    wp_seq_eq wp_skip_eq
  lemmas [vcg_unfolds] = wlp_assign_eq                  wp_assign_eq
  
  definition GOAL_INDICATION :: "string \<Rightarrow> bool" ("\<paragraph>_")
    where "GOAL_INDICATION _ \<equiv> True"
  
  lemma move_goal_indication_to_front[simp]: 
    "NO_MATCH (\<paragraph>x) P \<Longrightarrow> (P\<Longrightarrow>\<paragraph>n\<Longrightarrow>PROP Q) \<equiv> (\<paragraph>n \<Longrightarrow> P \<Longrightarrow> PROP Q)"  
    by (rule swap_prems_eq)
    (* TODO: Would like to use PROP P here, to also move over 
      meta-premises like \<open>\<And>x. a\<Longrightarrow>b\<close>, but \<open>NO_MATCH\<close> requires type! *)
      
    
  text \<open>Rules combined with case splitting\<close>    
  lemma wlp_whileI:
    assumes INIT: "\<paragraph>''Invar initial'' \<Longrightarrow> I \<ss>\<^sub>0"
    assumes STEP: "\<And>\<ss>. \<lbrakk> \<paragraph>''Invar pres''; I \<ss>; bval b \<ss> \<rbrakk> \<Longrightarrow> wlp c I \<ss>"
    assumes FINAL: "\<And>\<ss>. \<lbrakk> \<paragraph>''Invar post''; I \<ss>; \<not>bval b \<ss> \<rbrakk> \<Longrightarrow> Q \<ss>"
    shows "wlp (WHILE b DO c) Q \<ss>\<^sub>0"
    using assms wlp_whileI' GOAL_INDICATION_def by auto

    
    
  lemma wlp_ifI[vcg_rules]: 
    assumes "\<lbrakk>\<paragraph>''if-true''; bval b s\<rbrakk> \<Longrightarrow> wlp c\<^sub>1 Q s" 
    assumes "\<lbrakk>\<paragraph>''if-false''; \<not>bval b s\<rbrakk> \<Longrightarrow> wlp c\<^sub>2 Q s"
    shows "wlp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    using assms by (simp add: wlp_eq' GOAL_INDICATION_def)
  
  lemma wp_whileI:
    assumes WF: "\<paragraph>''Well-Founded'' \<Longrightarrow> wf R"
    assumes INIT: "\<paragraph>''Invar initial'' \<Longrightarrow>I \<ss>\<^sub>0"
    assumes STEP: "\<And>\<ss>. \<lbrakk> \<paragraph>''Invar pres''; I \<ss>; bval b \<ss> \<rbrakk> \<Longrightarrow> wp c (\<lambda>\<ss>'. I \<ss>' \<and> (\<ss>',\<ss>)\<in>R) \<ss>"
    assumes FINAL: "\<And>\<ss>. \<lbrakk> \<paragraph>''Invar post''; I \<ss>; \<not>bval b \<ss> \<rbrakk> \<Longrightarrow> Q \<ss>"
    shows "wp (WHILE b DO c) Q \<ss>\<^sub>0"
    using assms wp_whileI' GOAL_INDICATION_def by auto
  
  lemma wp_ifI[vcg_rules]: 
    assumes "\<lbrakk>\<paragraph>''if-true''; bval b s\<rbrakk> \<Longrightarrow> wp c\<^sub>1 Q s" 
    assumes "\<lbrakk>\<paragraph>''if-false''; \<not>bval b s\<rbrakk> \<Longrightarrow> wp c\<^sub>2 Q s"
    shows "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    using assms by (simp add: wp_eq' GOAL_INDICATION_def)
  
  
  subsection \<open>Annotated Loop Invariants\<close>  
    
  named_theorems annotation_defs \<open>Definitions of Annotations\<close>
  
  lemmas wlp_while_annotI[vcg_rules] = wlp_whileI[of I,folded WHILE_annotI_def[of I]] 
    for I :: "state \<Rightarrow> bool"
  
  lemmas wp_while_annotRVI[vcg_rules] = 
    wp_whileI[of "inv_image R V" I,unfolded annotate_whileRVI[of R V I], OF wf_inv_image] 
      for R :: "'a rel" and V :: "state \<Rightarrow> 'a" and I :: "state \<Rightarrow> bool"
  
  lemmas wp_while_annotVI[vcg_rules] = 
    wp_whileI[of "inv_image less_than V" I,unfolded annotate_whileVI[of V I], OF wf_inv_image[OF wf_less_than]] 
      for V :: "state \<Rightarrow> nat" and I :: "state \<Rightarrow> bool"
  
  
subsection \<open>Ad-Hoc Regression Tests\<close>

experiment
begin

program_def p1 = \<open>n = n + 1\<close>

program_spec (partial) p2
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @invariant \<open>n\<ge>0\<close> { n=n-1 }\<close>
  by vcg

program_spec p2'
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @variant \<open>nat n\<close> @invariant \<open>n\<ge>0\<close> { n=n-1 }\<close>
  by vcg
  
program_spec p2''
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @relation \<open>measure nat\<close> @variant \<open>n\<close> @invariant \<open>n\<ge>0\<close> { n=n-1 }\<close>
  by vcg
  
    
lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib

(* We've made the program a little larger \<dots> *)
program_spec exp_count_up
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
    a = 1;
    c = 0;
    while (c<n) 
      @variant \<open>nat (n-c)\<close> 
      @invariant \<open>n=n\<^sub>0 \<and> 0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>    
    {
      a=2*a;
      
      {
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      skip
      };
      
      c=c+1
    }
  \<close>
  apply vcg
  by (auto simp: algebra_simps nat_distribs)

end

end
