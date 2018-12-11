section \<open>Semantics of IMP\<close>
theory Semantics
imports Syntax "HOL-Eisbach.Eisbach_Tools" 
begin

subsection \<open>State\<close>
type_synonym state = "vname \<Rightarrow> val"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"


  
subsection \<open>Arithmetic Expressions\<close>

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" 
| "aval (V x) s = s x" 
| "aval (Unop f a\<^sub>1) s = f (aval a\<^sub>1 s)"
| "aval (Binop f a\<^sub>1 a\<^sub>2) s = f (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

subsection \<open>Boolean Expressions\<close>

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v" 
| "bval (Not b) s = (\<not> bval b s)" 
| "bval (BBinop f b\<^sub>1 b\<^sub>2) s = f (bval b\<^sub>1 s) (bval b\<^sub>2 s)" 
| "bval (Cmpop f a\<^sub>1 a\<^sub>2) s = f (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

subsection \<open>Big-Step Semantics\<close>

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  Skip: "(SKIP,s) \<Rightarrow> s" 
| Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" 
| Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" 
| IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" 
| IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" 
| WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" 
| WhileTrue: "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
    \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

subsubsection \<open>Proof Automation\<close>    
    
declare big_step.intros [intro]
lemmas big_step_induct[induct set] = big_step.induct[split_format(complete)]

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

subsubsection \<open>Automatic Derivation\<close>
  (* Testing the programs by constructing big-step derivations automatically *)    
  
  (* This rule is used to enforce simplification of the newly generated state, before passing it on *)
  lemma Assign': "s' = s(x:=aval a s) \<Longrightarrow> (x ::= a, s) \<Rightarrow> s'" by auto
  
  method big_step = 
    rule Skip Seq 
  | (rule Assign', (simp;fail)) 
  | (rule IfTrue IfFalse WhileTrue WhileFalse), (simp;fail)
  (*| (simp only: While_Annot_def)*)
      
  (* TODO: Make this work nicely with scopes! *)
  
  schematic_goal "(\<^imp>\<open>
    a=1;
    while (n>0) {
      a=a+a;
      n=n-1
    }
  \<close>,<''n'':=5>) \<Rightarrow> ?s"  
    by big_step+



subsection \<open>Command Equivalence\<close>

definition
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"

lemma equivI[intro?]: "\<lbrakk>
  \<And>s t. (c,s) \<Rightarrow> t \<Longrightarrow> (c',s) \<Rightarrow> t; 
  \<And>s t. (c',s) \<Rightarrow> t \<Longrightarrow> (c,s) \<Rightarrow> t\<rbrakk> 
  \<Longrightarrow> c \<sim> c'"  
  by (auto simp: equiv_c_def)
  
lemma equivD[dest]: "c \<sim> c' \<Longrightarrow> (c,s) \<Rightarrow> t \<longleftrightarrow> (c',s) \<Rightarrow> t"  
  by (auto simp: equiv_c_def)

text \<open>Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive.\<close>

lemma equiv_refl[simp, intro!]:  "c \<sim> c" by (blast intro: equivI)
lemma equiv_sym[sym]:   "(c \<sim> c') \<Longrightarrow> (c' \<sim> c)" by (blast intro: equivI)
lemma equiv_trans[trans]: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by (blast intro: equivI)

subsubsection \<open>Basic Equivalences\<close>
lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
  by rule blast+
  (*by (blast intro!: equivI)*)

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by (blast intro!: equivI)

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by (blast intro!: equivI)


lemma sim_while_cong_aux:
  "\<lbrakk>(WHILE b DO c,s) \<Rightarrow> t; bval b = bval b'; c \<sim> c' \<rbrakk> \<Longrightarrow>  (WHILE b' DO c',s) \<Rightarrow> t"
  apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
  apply auto
  done

lemma sim_while_cong: "bval b = bval b' \<Longrightarrow> c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b' DO c'"
  using equiv_c_def sim_while_cong_aux by auto

subsection "Execution is deterministic"

text \<open>This proof is automatic.\<close>

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  apply (induction arbitrary: u rule: big_step.induct) 
  apply blast+
  done

subsection \<open>Weakest Precondition\<close>  
  
  text \<open>Weakest precondition: 
    \<open>c\<close> terminates with a state that satisfies \<open>Q\<close>, when started from \<open>s\<close>\<close>
  definition "wp c Q s \<equiv> \<exists>t. (c,s) \<Rightarrow> t \<and> Q t"
    \<comment> \<open>Note that this definition exploits that the semantics is deterministic! 
      In general, we must ensure absence of infinite executions\<close>
    
  text \<open>Weakest liberal precondition: 
    If \<open>c\<close> terminates when started from \<open>s\<close>, the new state satisfies \<open>Q\<close>.\<close>    
  definition "wlp c Q s \<equiv> \<forall>t. (c,s) \<Rightarrow> t \<longrightarrow> Q t"
  
  subsubsection \<open>Basic Properties\<close>
  
  context 
    notes [abs_def,simp] = wp_def wlp_def
  begin
    lemma wp_imp_wlp: "wp c Q s \<Longrightarrow> wlp c Q s"
      using big_step_determ by auto
      
    lemma wlp_and_term_imp_wp: "wlp c Q s \<and> (c,s) \<Rightarrow> t \<Longrightarrow> wp c Q s" by auto    
    
    lemma wp_equiv: "c \<sim> c' \<Longrightarrow> wp c = wp c'" by auto
    lemma wp_conseq: "wp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wp c Q s" by auto
    lemma wp_equiv_iff: "wp c = wp c' \<longleftrightarrow> c \<sim> c'"
      unfolding equiv_c_def using big_step_determ by (auto; metis)
    
      
    lemma wlp_equiv: "c \<sim> c' \<Longrightarrow> wlp c = wlp c'" by auto
    lemma wlp_conseq: "wlp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wlp c Q s" by auto
    lemma wlp_equiv_iff: "wlp c = wlp c' \<longleftrightarrow> c \<sim> c'" 
      by (metis wlp_equiv equiv_c_def wlp_def)
    
      
  
  subsubsection \<open>Unfold Rules\<close>
    lemma wp_skip_eq: "wp SKIP Q s = Q s" by auto
    lemma wp_assign_eq: "wp (x::=a) Q s = Q (s(x:=aval a s))" by auto
    lemma wp_seq_eq: "wp (c\<^sub>1;;c\<^sub>2) Q s = wp c\<^sub>1 (wp c\<^sub>2 Q) s" by auto
    lemma wp_if_eq: "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s 
      = (if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)" by auto
    
    lemmas wp_eq = wp_skip_eq wp_assign_eq wp_seq_eq
    lemmas wp_eq' = wp_eq wp_if_eq
    
    lemma wlp_skip_eq: "wlp SKIP Q s = Q s" by auto
    lemma wlp_assign_eq: "wlp (x::=a) Q s = Q (s(x:=aval a s))" by auto
    lemma wlp_seq_eq: "wlp (c\<^sub>1;;c\<^sub>2) Q s = wlp c\<^sub>1 (wlp c\<^sub>2 Q) s" by auto
    lemma wlp_if_eq: "wlp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s 
      = (if bval b s then wlp c\<^sub>1 Q s else wlp c\<^sub>2 Q s)" by auto
      
          
    lemmas wlp_eq = wlp_skip_eq wlp_assign_eq wlp_seq_eq
    lemmas wlp_eq' = wlp_eq wlp_if_eq
  end
  
  lemma wlp_while_unfold: "wlp (WHILE b DO c) Q s = (if bval b s then wlp c (wlp (WHILE b DO c) Q) s else Q s)"
    apply (subst wlp_equiv[OF while_unfold])
    apply (simp add: wlp_eq')
    done
  
  lemma wp_while_unfold: "wp (WHILE b DO c) Q s = (if bval b s then wp c (wp (WHILE b DO c) Q) s else Q s)"
    apply (subst wp_equiv[OF while_unfold])
    apply (simp add: wp_eq')
    done
  
subsection \<open>Invariants for While-Loops\<close>
    
  subsubsection \<open>Partial Correctness\<close>
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

  (* Short proof (not the shortest possible one ;) ) *)
  lemma 
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp c I s else Q s)"
    shows "wlp (WHILE b DO c) Q s\<^sub>0"
    using STEP
    unfolding wlp_def
    apply clarify subgoal premises prems for t
      using prems(2,1) INIT
      by (induction "WHILE b DO c" s\<^sub>0 t rule: big_step_induct; force simp: wlp_def)
    done
    
  subsubsection \<open>Total Correctness\<close>
  
  lemma wp_whileI':
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

  (* Short Proof *)  
  lemma 
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wp c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s else Q s)"
    shows "wp (WHILE b DO c) Q s\<^sub>0"
    using WF INIT 
    apply induction
    apply (subst wp_while_unfold)
    by (smt STEP wp_conseq)
    
    
  subsubsection \<open>Standard Forms of While Rules\<close>  
  lemma wlp_whileI:
    assumes INIT: "I \<ss>\<^sub>0"
    assumes STEP: "\<And>\<ss>. \<lbrakk>I \<ss>; bval b \<ss> \<rbrakk> \<Longrightarrow> wlp c I \<ss>"
    assumes FINAL: "\<And>\<ss>. \<lbrakk> I \<ss>; \<not>bval b \<ss> \<rbrakk> \<Longrightarrow> Q \<ss>"
    shows "wlp (WHILE b DO c) Q \<ss>\<^sub>0"
    using assms wlp_whileI' by auto
    
    
  lemma wp_whileI:
    assumes WF: "wf R"
    assumes INIT: "I \<ss>\<^sub>0"
    assumes STEP: "\<And>\<ss>. \<lbrakk>I \<ss>; bval b \<ss> \<rbrakk> \<Longrightarrow> wp c (\<lambda>\<ss>'. I \<ss>' \<and> (\<ss>',\<ss>)\<in>R) \<ss>"
    assumes FINAL: "\<And>\<ss>. \<lbrakk> I \<ss>; \<not>bval b \<ss> \<rbrakk> \<Longrightarrow> Q \<ss>"
    shows "wp (WHILE b DO c) Q \<ss>\<^sub>0"
    using assms wp_whileI' by auto

end
