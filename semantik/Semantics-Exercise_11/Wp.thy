theory Wp
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
    using big_step_determ by auto
    
  lemma wlp_and_term_imp_wp: "wlp c Q s \<and> (c,s) \<Rightarrow> t \<Longrightarrow> wp c Q s"  
    unfolding wp_def wlp_def
    by auto    
  
  lemma wp_equiv: "c \<sim> c' \<Longrightarrow> wp c = wp c'"
    by (intro ext) (auto simp: wp_def)
      
  lemma wp_conseq: "wp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wp c Q s"
    by (auto simp: wp_def)
    
  subsection \<open>Weakest Preconditions of Loop-Free Commands\<close>  
    
  context 
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


  subsection \<open>Weakest Liberal Precondition of While\<close>
      
  lemma wlp_while_unfold: "wlp (WHILE b DO c) Q s = (if bval b s then wlp c (wlp (WHILE b DO c) Q) s else Q s)"
    apply (subst wlp_equiv[OF while_unfold])
    apply (simp add: wlp_eq')
    done
  
  lemma wlp_whileI':
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp c I s else Q s)"
    shows "wlp (WHILE b DO c) Q s\<^sub>0"
    unfolding wlp_def
  proof clarify
    fix t
    assume "(WHILE b DO c, s\<^sub>0) \<Rightarrow> t"
    thus "Q t" using INIT
    proof (induction "WHILE b DO c" s\<^sub>0 t rule: big_step_induct)
      case (WhileFalse s) with STEP show "Q s" by auto
    next
      case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
      
      from STEP[OF \<open>I s\<^sub>1\<close>] \<open>bval b s\<^sub>1\<close> have "wlp c I s\<^sub>1" by simp
      with \<open>(c, s\<^sub>1) \<Rightarrow> s\<^sub>2\<close> have "I s\<^sub>2" unfolding wlp_def by blast
      moreover note \<open>I s\<^sub>2 \<Longrightarrow> Q s\<^sub>3\<close>
      ultimately show "Q s\<^sub>3" by blast
    qed
  qed
  (** Challenge: Who finds the shortest proof for wlp_whileI'?
    We'll count the number of non-whitespace characters, from everything behind the \<open>shows-line\<close>,
    including the final done, or by, or qed.
    
    The proof must be placed at this point in the theory, i.e., only use lemmas that
    are available here!
  *)


lemma wlp_untilI':
  assumes INIT: "I s\<^sub>0"
  assumes STEP: "\<And>s. I s \<Longrightarrow> wlp c (\<lambda>s'. if bval b s' then Q s' else I s') s"
  shows "wlp (DO c UNTIL b) Q s\<^sub>0"
  unfolding wlp_def
proof clarify
  fix t
  assume "(DO c UNTIL b, s\<^sub>0) \<Rightarrow> t"
  thus "Q t" using INIT
  proof (induction "DO c UNTIL b" s\<^sub>0 t rule: big_step_induct)
    case (UntilTrue s s')
    with STEP[OF \<open>I s\<close>] show ?case
      unfolding wlp_def by auto
  next
    case (UntilFalse s s' t)
    with STEP[OF \<open>I s\<close>] have "I s'"
      unfolding wlp_def by auto
    then show ?case
      by (rule UntilFalse)
  qed
qed

section \<open>Proving Partial Correctness\<close>

  
  text \<open>Equivalent form of while-rule, where invariant preservation assumption is independent of postcondition.\<close>
  lemma wlp_whileI:
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. \<lbrakk> I s; bval b s \<rbrakk> \<Longrightarrow> wlp c I s"
    assumes FINAL: "\<And>s. \<lbrakk> I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    shows "wlp (WHILE b DO c) Q s\<^sub>0"
    using assms wlp_whileI' by auto
  

  text \<open>Equivalent form of if rule, with splitting\<close>
  lemma wlp_ifI: "\<lbrakk>bval b s \<Longrightarrow> wlp c\<^sub>1 Q s; \<not>bval b s \<Longrightarrow> wlp c\<^sub>2 Q s\<rbrakk> \<Longrightarrow> wlp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    by (simp add: wlp_eq')

  
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

lemma wp_until_unfold:
  "wp (DO c UNTIL b) Q s = wp c (\<lambda> s. if bval b s then Q s else wp (DO c UNTIL b) Q s) s"
  apply (subst wp_equiv[OF until_unfold])
  apply (simp add: wp_if_eq[abs_def] wp_eq')
  done

lemma
  assumes WF: "wf R"
  assumes INIT: "I s\<^sub>0"
  assumes STEP: "\<And>s. I s \<Longrightarrow> wp c (\<lambda>s'. if bval b s' then Q s' else I s' \<and> (s',s)\<in>R) s"
  shows "wp (DO c UNTIL b) Q s\<^sub>0"
  using WF INIT 
  apply induction
  apply (subst wp_until_unfold)
  by (smt STEP wp_conseq)

lemma wp_untilI':
  assumes WF: "wf R"
  assumes INIT: "I s\<^sub>0"
  assumes STEP: "\<And>s. I s \<Longrightarrow> wp c (\<lambda>s'. if bval b s' then Q s' else I s' \<and> (s',s)\<in>R) s"
  shows "wp (DO c UNTIL b) Q s\<^sub>0"
  using WF INIT
proof induction
  case (less s)
  show "wp (DO c UNTIL b) Q s"
  proof (rule wp_until_unfold[THEN iffD2])
    show "wp c (\<lambda>s. if bval b s then Q s else wp (DO c UNTIL b) Q s) s"
      apply (rule wp_conseq)
       apply (rule STEP[OF \<open>I s\<close>])
      apply clarsimp
      apply (rule less; assumption)
      done
  qed
qed


subsection \<open>Completeness of Until-Rule\<close>

lemma wlp_until_unfold:
  "wlp (DO c UNTIL b) Q s = wlp c (\<lambda> s. if bval b s then Q s else wlp (DO c UNTIL b) Q s) s"
  apply (subst wlp_equiv[OF until_unfold])
  apply (simp add: wlp_if_eq[abs_def] wlp_eq')
  done

text \<open>Idea: Use \<open>wlp\<close> as invariant\<close>
lemma wlp_untilI'_complete:
  assumes "wlp (DO c UNTIL b) Q s\<^sub>0"
  obtains I where
    "I s\<^sub>0"
    "\<And>s. I s \<Longrightarrow> wlp c (\<lambda>s'. if bval b s' then Q s' else I s') s"
proof
  let ?I = "wlp (DO c UNTIL b) Q"
  {
    show "?I s\<^sub>0" by fact
  next
    fix s
    assume "?I s"
    then show "wlp c (\<lambda>s'. if bval b s' then Q s' else ?I s') s"
      by (subst (asm) wlp_until_unfold) 
  }  
qed

text \<open>Idea: Remaining loop iterations as variant\<close>

inductive count_it for b c where
  "(c, s) \<Rightarrow> s' \<Longrightarrow> bval b s' \<Longrightarrow> count_it b c s 1"
| "\<lbrakk>(c,s) \<Rightarrow> s'; \<not> bval b s'; count_it b c s' n \<rbrakk> \<Longrightarrow> count_it b c s (Suc n )"  

lemma count_it_determ:
  "count_it b c s n \<Longrightarrow> count_it b c s n' \<Longrightarrow> n' = n"
  by (induction arbitrary: n' rule: count_it.induct; metis big_step_determ count_it.cases)

lemma count_it_ex:   
  assumes "(DO c UNTIL b,s) \<Rightarrow> t"
  shows "\<exists>n. count_it b c s n"
  using assms
  apply (induction "DO c UNTIL b" s t arbitrary: b c rule: big_step_induct)
  apply (auto intro: count_it.intros)
  done

definition "variant b c s \<equiv> THE n. count_it b c s n"

lemma variant_decreases:
  assumes STEPB: "\<not> bval b s'" 
  assumes STEPC: "(c,s) \<Rightarrow> s'" 
  assumes TERM: "(DO c UNTIL b,s') \<Rightarrow> t"
  shows "variant b c s' < variant b c s"
proof -
  from count_it_ex[OF TERM] obtain n' where CI': "count_it b c s' n'" ..
  moreover from count_it.intros(2)[OF STEPC STEPB this] have "count_it b c s (Suc n')" .
  ultimately have "variant b c s' = n'" "variant b c s = Suc n'" 
    unfolding variant_def using count_it_determ by blast+
  thus ?thesis by simp 
qed

lemma wp_whileI'_complete:
  fixes b c
  defines "R\<equiv>measure (variant b c)"
  assumes "wp (DO c UNTIL b) Q s\<^sub>0"
  obtains I where
    "wf R"
    "I s\<^sub>0"
    "\<And>s. I s \<Longrightarrow> wp c (\<lambda>s'. if bval b s' then Q s' else I s' \<and> (s',s)\<in>R) s"
proof   
  show \<open>wf R\<close> unfolding R_def by auto
  let ?I = "wp (DO c UNTIL b) Q"
  {
    show "?I s\<^sub>0" by fact
  next
    fix s
    assume "?I s"
    then show "wp c (\<lambda>s'. if bval b s' then Q s' else ?I s' \<and> (s',s)\<in>R) s"
      apply (subst (asm) wp_until_unfold) 
      apply clarsimp
      apply (auto simp: wp_def R_def intro: variant_decreases split: if_split_asm)
      done
  }  
qed

end