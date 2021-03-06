(**
  Partial file, to be completed during lecture or tutorial.
  See Wp.thy for completed version!
**)
theory Wp_Demo
imports Big_Step "HOL-Eisbach.Eisbach_Tools"
begin
  section \<open>Weakest Precondition\<close>

  subsection \<open>Weakest (liberal) Precondition\<close>

  text \<open>Weakest precondition: 
    \<open>c\<close> terminates with a state that satisfies \<open>Q\<close>, when started from \<open>s\<close>\<close>
  definition "wp c Q s \<equiv> \<exists>t. (c,s) \<Rightarrow> t \<and> Q t"
    \<comment> \<open>Note that this definition exploits that the semantics is deterministic! 
      In general, we must ensure absence of infinite executions\<close>
    
  text \<open>Weakest liberal precondition: 
    If \<open>c\<close> terminates when started from \<open>s\<close>, the new state satisfies \<open>Q\<close>.\<close>    
  definition "wlp c Q s \<equiv> \<forall>t. (c,s) \<Rightarrow> t \<longrightarrow> Q t"

  lemma wp_imp_wlp: "wp c Q s \<Longrightarrow> wlp c Q s"
    unfolding wp_def wlp_def
    apply auto
    apply(drule big_step_determ)
    apply assumption
    (* Some fact is missing here! *)
    oops
    
  lemma wlp_and_term_imp_wp: "wlp c Q s \<and> (c,s) \<Rightarrow> t \<Longrightarrow> wp c Q s"  
    unfolding wp_def wlp_def
    by auto    

  (* this is extensionality
     \<forall> x.f x = g x \iff  f = g *) 
  lemma wp_equiv: "c \<sim> c' \<Longrightarrow> wp c = wp c'"
    apply(intro ext)
    apply(auto simp: wp_def)
  done

  lemma wp_conseq: "wp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wp c Q s"
    by (auto simp: wp_def)
    
  subsection \<open>Weakest Preconditions of Loop-Free Commands\<close>  
    
context 
    (* Here we allow automatic simps in the local context *)
    notes [simp] = wp_def wlp_def \<comment> \<open>Locally enable unfolding\<close>
  begin  
    lemma wp_skip_eq: "wp SKIP Q s = Q s" by auto
    lemma wp_assign_eq: "wp (x::=a) Q s = Q (s(x:=aval a s))" by auto
    lemma wp_seq_eq: "wp (c\<^sub>1;;c\<^sub>2) Q s = wp c\<^sub>1 (wp c\<^sub>2 Q) s" by auto
    lemma wp_if_eq: "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s = (if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)" by auto
    
    lemmas wp_eq = wp_skip_eq wp_assign_eq wp_seq_eq    
    lemmas wp_eq' = wp_eq wp_if_eq
    
    text \<open>The same for \<open>wlp\<close>\<close>
    lemma wlp_skip_eq: "wlp SKIP Q s = Q s" by auto
    lemma wlp_assign_eq: "wlp (x::=a) Q s = Q (s(x:=aval a s))" by auto
    lemma wlp_seq_eq: "wlp (c\<^sub>1;;c\<^sub>2) Q s = wlp c\<^sub>1 (wlp c\<^sub>2 Q) s" by auto
    lemma wlp_if_eq: "wlp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s = (if bval b s then wlp c\<^sub>1 Q s else wlp c\<^sub>2 Q s)" by auto
    
    lemmas wlp_eq = wlp_skip_eq wlp_assign_eq wlp_seq_eq    
    lemmas wlp_eq' = wlp_eq wlp_if_eq
    
    lemma wlp_equiv: "c \<sim> c' \<Longrightarrow> wlp c = wlp c'" by (intro ext) auto
    lemma wlp_conseq: "wlp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wlp c Q s" by auto
  end    

  (* We don't unfold all the definitions that unfold wp 
     we use this unfolding for specific properties and then
     I just reason about what I proved 

     This is also important with writing our theories, 
     otherwise we can get huge goals that will not be solved
     by auto *)

  subsection \<open>Weakest Liberal Precondition of While\<close>
      
  lemma wlp_while_unfold: 
    "wlp (WHILE b DO c) Q s 
    = (if bval b s then wlp c (wlp (WHILE b DO c) Q) s else Q s)"
    apply (subst wlp_equiv[OF while_unfold])
    apply (simp add: wlp_eq')
    done
  
  lemma wlp_whileI':
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp c I s else Q s)"
    shows "wlp (WHILE b DO c) Q s\<^sub>0"
    unfolding wlp_def
  proof clarify (* converts from the HOL level to the meta-level *)
    fix t
    assume "(WHILE b DO c, s\<^sub>0) \<Rightarrow> t"
    thus "Q t" using INIT
    proof (induction "WHILE b DO c" s\<^sub>0 t rule: big_step_induct)
      case (WhileFalse s) show "Q s" 
        
        sorry
    next
      case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)

      show "Q s\<^sub>3" sorry
    qed
  qed
  (** Challenge: Who finds the shortest proof for wlp_whileI'?
    We'll count the number of non-whitespace characters, from everything behind the \<open>shows-line\<close>,
    including the final done, or by, or qed.
    
    The proof must be placed at this point in the theory, i.e., only use lemmas that
    are available here!
  *)  
  
  
  

section \<open>Proving Partial Correctness\<close>

  
  text \<open>Equivalent form of while-rule, where invariant preservation
     assumption is independent of postcondition.\<close>
  lemma wlp_whileI:
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. \<lbrakk> I s; bval b s \<rbrakk> \<Longrightarrow> wlp c I s"
    assumes FINAL: "\<And>s. \<lbrakk> I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    shows "wlp (WHILE b DO c) Q s\<^sub>0"
    using assms wlp_whileI' by auto
  

  text \<open>Equivalent form of if rule, with splitting\<close>
  lemma wlp_ifI: "\<lbrakk>
      bval b s \<Longrightarrow> wlp c\<^sub>1 Q s; 
      \<not>bval b s \<Longrightarrow> wlp c\<^sub>2 Q s\<rbrakk> 
    \<Longrightarrow> wlp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    by (simp add: wlp_eq')
    
    
  subsection \<open>Example Programs\<close>  
  
  definition "prog_min \<equiv> 
    IF (Less (V ''x'') (V ''y'')) THEN ''z'' ::= V ''x'' 
    ELSE ''z'' ::= V ''y''"
  
  definition "prog_exp \<equiv> 
    ''a''::=N 1;; 
    WHILE Less (N 0) (V ''n'') DO (
      ''a'' ::= Plus (V ''a'') (V ''a'');;
      ''n'' ::= Plus (V ''n'') (N (-1))
    )"  

  subsection \<open>Automatic Execution of Big-Step\<close>  
    
  (* Testing the programs by constructing big-step derivations automatically *) 
  (* tries to apply the rules one after the other. 
     in second rule simp? will try to simp but if it fase it continues
    then tries if or while rule. then should follow a simp that if failing
    will lead to the whole thing to fail 

    se can write apply big_step now
  *)
  method big_step = 
    rule Skip Seq 
  | (rule Assign, simp?) 
  | (rule IfTrue IfFalse WhileTrue WhileFalse), (simp;fail)
      
  schematic_goal "(prog_exp,<''n'':=0>) \<Rightarrow> ?s"  
    unfolding prog_exp_def
    by big_step+ (* we just need three big_steps *)
    
    
    
  subsection \<open>Manual Correctness Proofs\<close>  
  
  (* We'll need these lemmas later! *)
  lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib

  (* no preconditions
     if i a run the program in s then i get a set a state such that
     the variable z contains the minimum between x an y *)
  lemma "wlp (prog_min) (\<lambda>s'. s' ''z'' = min (s ''x'') (s ''y'')) s"
    unfolding prog_min_def
    apply(subst wlp_if_eq) (*unfold the top if*)
    (* subst applies equalities by rewriting *)
    apply(split if_split) (*split the if then else*)
    apply(intro conjI impI) (*remove conjunction and move to preconditions*)
    (* in one step apply(rule wlp_ifI) *)
    apply(subst wlp_assign_eq) (* we get the updated state *)
    apply(simp only: bval.simps aval.simps) (* apply the simplifier to remove the aval and bval *)
    (* shorter, do for each direction
       apply(subst wlp_assing_eq)
       apply simp
    *)
    (* Use rule, subst, and simp for VCs *)
    oops
    
    
    
  lemma "s ''n'' \<ge> 0 \<Longrightarrow> wlp prog_exp (\<lambda>s'. s' ''a'' = 2^nat (s ''n'')) s"  
    unfolding prog_exp_def
    apply(subst wlp_seq_eq)
    apply(subst wlp_assign_eq)
    apply(rule wlp_whileI[where I=I]) 
    (* apply while rule with automatic if splitting and instantiate schematic
       variables (which could be \<lambda>x.true) *)
    apply simp defer
    apply (subst wlp_seq_eq)
    apply (subst wlp_assign_eq)
    apply (subst wlp_assign_eq)
    defer 
    defer
    (* now we have to insert an invariant above so that the property holds
       subgoal focus on one subgoal in isolation
       suboal apply simp done 
       here we take into account that a = 2^i where i is the number of iteration
       we have done. since the loop counts down, i = current_n - old_n *)
    apply(rule wlp_whileI[I = see webpage])
    apply(subst wlp_assign_eq; clarsimp?) 
    (* ; will apply the rule to all the subgoals *) 
    (* there is a blowup in the above procedure because we get 2 s each
       time we apply the assign rule, here is the way to cut it *)
    apply(subst wlp_eq_eq)
    apply(subst wlp_assign_eq; clarsimp?)
    apply(subst wlp_assing_eq; clarsimp?)
    apply(auto simp: nat_distribs algebra_simps)
    done
    
    (* Use rule, subst, and simp for VCs. Try (auto simp: nat_distribs algebra_simps) for final VC!
      What might be a good invariant? Insert symbolic I first.
    *)
  oops
    
    
  subsection \<open>Automating the Profs\<close>  

  
  (* Intermediate goals got quite big: Lets simplify them while we go! *)  
    
  lemma "s ''n'' \<ge> 0 \<Longrightarrow> wlp prog_exp (\<lambda>s'. s' ''a'' = 2^nat (s ''n'')) s"  
    unfolding prog_exp_def
    (* Apply clarsimp after assign and while ... not needed for seq, skip! *)
    oops

        
  (* Automating the VCG *)  

  (*
    Note: This uses (a simple fragment of) the Eisbach language. 
    See Documentation/Tutorials/eisbach if you want to know more!
  *)
  (*
    the command method is imported by (see top of the file)
    it implement the eisbach (afluent to isar) methodology 
    it was implement for the derivation of verification conditions *)
      
  named_theorems vcg_rules  
    
  declare wlp_ifI[vcg_rules]
  
method vcg_step declares vcg_rules = 
      simp only: wlp_seq_eq wlp_skip_eq    wp_seq_eq wp_skip_eq 
    | subst wlp_assign_eq                  wp_assign_eq 
    | rule vcg_rules
    (* only to avoid blowup 
       for assignment we want to apply only one step with subst
       finally i apply one of the introduction rules we have declared 
       declares is used to add more rules 
    *)
    \<comment> \<open>One step. Note that we unfold as many seqs or skips as possible, as these won't enlarge the subgoal, 
      so no intermediate simplification is required\<close>
  
  method vcg declares vcg_rules = ( (vcg_step; vcg)? )
    \<comment> \<open>Recursively apply all possible steps, without intermediate simplification\<close>

  (* does simplification before each step *)
  method smartvcg declares vcg_rules = ( (vcg_step; clarsimp?; smartvcg)? )
    \<comment> \<open>Recursively apply all possible steps, with intermediate simplification\<close>

  (* we remove the semantics features with the verification condition 
     generator, and now everything is written isabelle.
 
     the idea is that verifying those is enough to proof correctness *)
    
  lemma "wlp (prog_min) (\<lambda>s'. s' ''z'' = min (s ''x'') (s ''y'')) s"
    unfolding prog_min_def
    (* apply vcg *)
    apply smartvcg
    done

  lemma "s ''n'' \<ge> 0 \<Longrightarrow> wlp prog_exp (\<lambda>s'. s' ''a'' = 2^nat (s ''n'')) s"  
    unfolding prog_exp_def
    (* Provide the **instantiated** while rule in an ad-hoc manner *)
    apply (smartvcg vcg_rules: 
      wlp_whileI[where 
          I="\<lambda>s'. s' ''a'' = 2 ^ nat (s ''n'' - s' ''n'') \<and> 0 \<le> s' ''n'' \<and> s' ''n'' \<le> s ''n''"
        ]
    )
    by (auto simp: algebra_simps nat_distribs) 
    
    
  subsection \<open>Annotation of Loop Invariants\<close>  
    
  (* Better: Annotate the invariants to the loops before proving. 
    (Control which loop gets which invariant, if there are many loops) *)  

  (* redefined while taken a predicate *)
    
  definition "WHILE_annotI (I::state \<Rightarrow> bool) \<equiv> While"
  lemmas wlp_annotate_while = WHILE_annotI_def[symmetric]
  lemmas wlp_while_annotI[vcg_rules] = wlp_whileI[of I,folded WHILE_annotI_def[of I]] for I
  (* a more robust way to annotate the program is to use rewrite *)
    
  lemma "s ''n'' \<ge> 0 \<Longrightarrow> wlp prog_exp (\<lambda>s'. s' ''a'' = 2^nat (s ''n'')) s"  
    unfolding prog_exp_def
    apply (subst wlp_annotate_while[where 
          I="\<lambda>s'. s' ''a'' = 2 ^ nat (s ''n'' - s' ''n'') \<and> 0 \<le> s' ''n'' \<and> s' ''n'' \<le> s ''n''" 
        ])
    apply smartvcg  
    by (auto simp: algebra_simps nat_distribs) 
    
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
section \<open>Total Correctness\<close>  
  
  subsection \<open>While-Rule for Total Correctness\<close>
  
  
  lemma wp_while_unfold: "wp (WHILE b DO c) Q s = (if bval b s then wp c (wp (WHILE b DO c) Q) s else Q s)"
    apply (subst wp_equiv[OF while_unfold])
    apply (simp add: wp_eq')
    done
  
  lemma wp_whileI':
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wp c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s else Q s)"
    shows "wp (WHILE b DO c) Q s\<^sub>0"
    using WF INIT 
    apply induction
    apply (subst wp_while_unfold)
    by (smt STEP wp_conseq)
    
    
  text \<open>Detailed Isar proof of @{thm [source] wp_whileI'}:\<close>
  lemma 
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wp c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s else Q s)"
    shows "wp (WHILE b DO c) Q s\<^sub>0"
    using WF INIT 
  proof induction
    case (less s)
    show "wp (WHILE b DO c) Q s" 
    proof (rule wp_while_unfold[THEN iffD2])
      show "if bval b s then wp c (wp (WHILE b DO c) Q) s else Q s" 
      proof (split if_split; intro allI impI conjI)
        assume [simp]: "bval b s"
        
        from STEP \<open>I s\<close> have "wp c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s" by simp
        thus "wp c (wp (WHILE b DO c) Q) s" proof (rule wp_conseq)
          fix s' assume "I s' \<and> (s',s)\<in>R"
          with less.IH show "wp (WHILE b DO c) Q s'" by blast
        qed
      next
        assume [simp]: "\<not>bval b s"
        from STEP \<open>I s\<close> show "Q s" by simp
      qed
    qed
  qed
          
  text \<open>Equivalent form of while-rule, where invariant preservation assumption 
    is independent of postcondition.\<close>
  lemma wp_whileI:
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. \<lbrakk> I s; bval b s \<rbrakk> \<Longrightarrow> wp c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s"
    assumes FINAL: "\<And>s. \<lbrakk> I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    shows "wp (WHILE b DO c) Q s\<^sub>0"
    using assms wp_whileI' by auto

  subsection \<open>Invariant Annotation and VCG setup\<close>    
    
  definition "WHILE_annot (R::state rel) (I::state \<Rightarrow> bool) \<equiv> While"
  lemmas wp_annotate_while = WHILE_annot_def[symmetric]
  lemmas wp_while_annotI[vcg_rules] = wp_whileI[of R I,folded WHILE_annot_def[of R I]] for R I

  text \<open>Equivalent form of if rule, with splitting\<close>
  lemma wp_ifI[vcg_rules]: "\<lbrakk>
      bval b s \<Longrightarrow> wp c\<^sub>1 Q s; 
      \<not>bval b s \<Longrightarrow> wp c\<^sub>2 Q s
    \<rbrakk> \<Longrightarrow> wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    by (simp add: wp_eq')

    
  subsection \<open>Example Proofs\<close>    
        
  (* No loop contained in this program! *)    
  lemma "wp (prog_min) (\<lambda>s'. s' ''z'' = min (s ''x'') (s ''y'')) s"
    unfolding prog_min_def
    by smartvcg

  lemma "s ''n'' \<ge> 0 \<Longrightarrow> wp prog_exp (\<lambda>s'. s' ''a'' = 2^nat (s ''n'')) s"  
    unfolding prog_exp_def
    apply (subst wp_annotate_while[where 
          I="\<lambda>s'. s' ''a'' = 2 ^ nat (s ''n'' - s' ''n'') \<and> 0 \<le> s' ''n'' \<and> s' ''n'' \<le> s ''n''" 
      and R = "measure (\<lambda>s. f s)"]
      )
    apply smartvcg  
    apply (auto simp: algebra_simps nat_distribs) 
    oops
    
  
    
end
