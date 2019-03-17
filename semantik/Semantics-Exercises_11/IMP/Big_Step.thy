(* Author: Gerwin Klein, Tobias Nipkow *)

theory Big_Step imports Com begin

subsection "Big-Step Semantics of Commands"

text \<open>
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first parameter is a tuple,
so the syntax becomes @{text "(c,s) \<Rightarrow> s'"}.
\<close>

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  Skip: "(SKIP,s) \<Rightarrow> s" |
  Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
  Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
  IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
  IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
  WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
  WhileTrue:
  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
    \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
  UntilFalse: 
  "\<lbrakk> \<not>bval b s\<^sub>2 ; (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (DO c UNTIL b, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
    \<Longrightarrow> (DO c UNTIL b, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
  UntilTrue: "\<lbrakk>(c,s) \<Rightarrow> s' ; bval b s'\<rbrakk> \<Longrightarrow> (DO c UNTIL b, s) \<Rightarrow> s'"

definition "w \<equiv> (WHILE ((Less (V ''x'') (N 5))) DO ''x'' ::= (Plus (V ''x'') (N 1)))"    
    
schematic_goal "(w,<''x'' := 4>) \<Rightarrow> ?s"
  unfolding w_def
  apply (rule WhileTrue)
  apply simp
  apply (rule Assign)
  apply simp
  apply (rule WhileFalse)
  apply simp
  done
    

lemma 1: "(c1;;c2,s) \<Rightarrow> t \<Longrightarrow> \<exists>s'. (c1,s) \<Rightarrow> s' \<and> (c2,s') \<Rightarrow> t"
  by (auto elim: big_step.cases)  
  
term "\<And>x. P x \<Longrightarrow> Q x"  
term "\<forall>x. P x \<Longrightarrow> Q x"  
term "\<forall>x. P x \<longrightarrow> Q x"  

lemma 
  assumes A: "(c1;;c2,s) \<Rightarrow> t"
  obtains s' where "(c1,s) \<Rightarrow> s'" "(c2,s') \<Rightarrow> t"
proof -
  thm that
  from 1[OF A] have "\<exists>s'. (c1,s) \<Rightarrow> s' \<and> (c2,s') \<Rightarrow> t" .
  then obtain s' where "(c1,s) \<Rightarrow> s' \<and> (c2,s') \<Rightarrow> t" ..
  from that[of s'] this show "thesis" by blast
qed
  
    
lemma 
  assumes A: "(c1;;c2,s) \<Rightarrow> t"
  assumes B: "\<And>s'. \<lbrakk> (c1,s) \<Rightarrow> s'; (c2,s') \<Rightarrow> t \<rbrakk> \<Longrightarrow> P"
  shows "P" 
proof -
  from 1[OF A] have "\<exists>s'. (c1,s) \<Rightarrow> s' \<and> (c2,s') \<Rightarrow> t" .
  then obtain s' where "(c1,s) \<Rightarrow> s' \<and> (c2,s') \<Rightarrow> t" ..
  from B[of s'] this show "P" by blast
qed
  
lemma 
  assumes "(IF b THEN c ELSE e, s) \<Rightarrow> t"
  obtains "bval b s" "(c,s) \<Rightarrow> t" 
        | "\<not>bval b s" "(e,s) \<Rightarrow> t"
proof -
  thm that 
  thm that(1)
  thm that(2)  
  
  show thesis
    using that assms
    by (auto elim: big_step.cases)
qed         
   
      
lemma
  assumes "(WHILE b DO c, s) \<Rightarrow> t"
  obtains
    "\<not>bval b s" "t=s"
  | s' where "bval b s" "(c,s) \<Rightarrow> s'" "(WHILE b DO c, s') \<Rightarrow> t"  
  using assms by (auto elim: big_step.cases)        
  
  
text\<open>Proof automation:\<close>

text \<open>The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules.\<close>
declare big_step.intros [intro]

text\<open>The standard induction rule 
@{thm [display] big_step.induct [no_vars]}\<close>

thm big_step.induct

text\<open>
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the @{text c}, @{text s},
and @{text s'} that we are likely to encounter. Splitting
the tuple parameter fixes this:
\<close>
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text \<open>
@{thm [display] big_step_induct [no_vars]}
\<close>


subsection "Rule inversion"

text\<open>What can we deduce from @{prop "(SKIP,s) \<Rightarrow> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE

text\<open>This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands:\<close>

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

thm big_step.cases

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
text\<open>Only [elim]: [elim!] would not terminate.\<close>
inductive_cases UntilE[elim]: "(DO c UNTIL b,s) \<Rightarrow> t"

text\<open>An automatic example:\<close>

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

text\<open>Rule inversion by hand via the ``cases'' method:\<close>

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  \<comment> \<open>inverting assms\<close>
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text \<open>An example combining rule inversion and derivations\<close>
lemma Seq_assoc:
  "((c1;; c2);; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  \<comment> \<open>The other direction is analogous\<close>
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed


subsection "Command Equivalence"

text \<open>
  We call two statements @{text c} and @{text c'} equivalent wrt.\ the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
\<close>

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
  
  
  
    
text \<open>
Warning: @{text"\<sim>"} is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
\<close>
lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN (c;; WHILE b DO c) ELSE SKIP)" (is "?w \<sim> ?iw")
proof 
  fix s t
  assume "(?w, s) \<Rightarrow> t"
  thus "(?iw, s) \<Rightarrow> t" 
  proof cases \<comment> \<open>rule inversion on \<open>(?w, s) \<Rightarrow> t\<close>\<close>
    case WhileFalse
    thus ?thesis by blast
  next
    case WhileTrue
    from \<open>bval b s\<close> \<open>(?w, s) \<Rightarrow> t\<close> obtain s' where
      "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
    \<comment> \<open>now we can build a derivation tree for the @{text IF}\<close>
    \<comment> \<open>first, the body of the True-branch:\<close>
    hence "(c;; ?w, s) \<Rightarrow> t" by (rule Seq)
    \<comment> \<open>then the whole @{text IF}\<close>
    with \<open>bval b s\<close> show ?thesis by (rule IfTrue)
  qed
next
  fix s t
  assume "(?iw, s) \<Rightarrow> t"
  thus "(?w, s) \<Rightarrow> t"
  proof cases \<comment> \<open>rule inversion on \<open>(?iw, s) \<Rightarrow> t\<close>\<close>
    case IfFalse
    hence "s = t" using \<open>(?iw, s) \<Rightarrow> t\<close> by blast
    thus ?thesis using \<open>\<not>bval b s\<close> by blast
  next
    case IfTrue
    \<comment> \<open>and for this, only the Seq-rule is applicable:\<close>
    from \<open>(c;; ?w, s) \<Rightarrow> t\<close> obtain s' where
      "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
    \<comment> \<open>with this information, we can build a derivation tree for @{text WHILE}\<close>
    with \<open>bval b s\<close> show ?thesis by (rule WhileTrue)
  qed
qed

text \<open>Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.\<close>

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
  by rule blast+
  (*by (blast intro!: equivI)*)

lemma until_unfold:
  "(DO c UNTIL b) \<sim> (c ;; IF b THEN SKIP ELSE DO c UNTIL b)"
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
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
 apply blast
apply blast
done

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by (blast intro: equivI sim_while_cong_aux equiv_sym)


subsection "Execution is deterministic"

text \<open>This proof is automatic.\<close>

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  apply (induction arbitrary: u  rule: big_step.induct) 
  apply(blast)+
  done

text \<open>
  This is the proof as you might present it in a lecture. The remaining
  cases are simple enough to be proved automatically:
\<close>

theorem
  "(c,s) \<Rightarrow> t  \<Longrightarrow>  (c,s) \<Rightarrow> t'  \<Longrightarrow>  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  \<comment> \<open>the only interesting case, @{text WhileTrue}:\<close>
  fix b c s s\<^sub>1 t t'
  \<comment> \<open>The assumptions of the rule:\<close>
  assume "bval b s" and "(c,s) \<Rightarrow> s\<^sub>1" and "(WHILE b DO c,s\<^sub>1) \<Rightarrow> t"
  \<comment> \<open>Ind.Hyp; note the @{text"\<And>"} because of arbitrary:\<close>
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s\<^sub>1"
  assume IHw: "\<And>t'. (WHILE b DO c,s\<^sub>1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  \<comment> \<open>Premise of implication:\<close>
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with \<open>bval b s\<close> obtain s\<^sub>1' where
      c: "(c,s) \<Rightarrow> s\<^sub>1'" and
      w: "(WHILE b DO c,s\<^sub>1') \<Rightarrow> t'"
    by auto
  from c IHc have "s\<^sub>1' = s\<^sub>1" by blast
  with w IHw show "t' = t" by blast
qed blast+ \<comment> \<open>prove the rest automatically\<close>

end
