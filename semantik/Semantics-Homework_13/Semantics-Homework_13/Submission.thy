theory Submission
  imports Defs
begin

paragraph \<open>Question 1\<close>

lemma aval_inv:
 "(c,s) \<Rightarrow> t \<Longrightarrow> vars c \<inter> vars a = {} \<Longrightarrow>  aval a s = aval a t" 
proof(induction  rule: big_step_induct)
  case (Assign x v s)
  then show ?case 
  proof(induction a s rule: aval.induct)
    case (3 a\<^sub>1 a\<^sub>2 s)
    then show ?case by (simp add: inf_sup_distrib1)
  qed auto   
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by force
qed auto

lemma bool_inv:
 "(c,s) \<Rightarrow> t \<Longrightarrow> vars c \<inter> vars b = {} \<Longrightarrow>  bval b s \<longleftrightarrow> bval b t" 
proof(induction  rule: big_step_induct)
  case (Assign x a s)
  then show ?case 
  proof(induction b s rule: bval.induct)
    case (4 a\<^sub>1 a\<^sub>2 s)
    from aval_inv[of "x ::= a" s "s(x := aval a s)" a\<^sub>1]
         aval_inv[of "x ::= a" s "s(x := aval a s)" a\<^sub>2]
         4
    have 1: "aval a\<^sub>1 s = aval a\<^sub>1 (s(x := aval a s))" "aval a\<^sub>2 s = aval a\<^sub>2 (s(x := aval a s))" by auto
    then have "(aval a\<^sub>1 s < aval a\<^sub>2 s) = (aval a\<^sub>1 (s(x := aval a s)) < aval a\<^sub>2 (s(x := aval a s)))" by simp
    then show ?case using bval.simps(4) by blast
  qed auto
qed auto
 
theorem ex1:
  "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> vars c \<inter> vars b = {} \<Longrightarrow> \<not> bval b s"
proof(induction "WHILE b DO c" s t rule: big_step_induct)
  case (WhileFalse s)
  then show ?case by simp 
next
  case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
  from WhileTrue.prems WhileTrue.hyps(5)
  have 1: "\<not> bval b s\<^sub>2" by simp
  from WhileTrue.prems WhileTrue.hyps(2) 
       bool_inv[of c s\<^sub>1 s\<^sub>2 b] 1
  show "\<not> bval b s\<^sub>1" by simp
qed
     

paragraph \<open>Question 2\<close>

fun no :: "com \<Rightarrow> bool" where
"no SKIP = True" |
"no (x::=a) = True" |
"no (c1;;c2) \<longleftrightarrow> no c1 \<and> no c2" |
"no (IF b THEN c1 ELSE c2) \<longleftrightarrow> no c1 \<and> no c2" |
"no (WHILE b DO c) = False"

theorem ex2:
  "no c \<Longrightarrow> \<forall> s. \<exists> t. (c, s) \<Rightarrow> t"
proof(induction c)
  case (Seq c1 c2)
  then have 0: "\<forall>s. \<exists>a. (c1, s) \<Rightarrow> a" 
               "\<forall>s. \<exists>a. (c2, s) \<Rightarrow> a" by auto
  {
    fix s
    from 0 obtain t1 t2 where 1: 
     "(c1, s) \<Rightarrow> t1" "(c2,t1) \<Rightarrow> t2" by blast
    then have "\<exists>a. (c1;;c2, s) \<Rightarrow> a" by auto  
  }   
  then show ?case by simp
next
  case (If b c1 c2)
  then have 0: "\<forall>s. \<exists>a. (c1, s) \<Rightarrow> a" 
               "\<forall>s. \<exists>a. (c2, s) \<Rightarrow> a" by auto
  {
    fix s
    from 0 obtain t1 t2 where 1: "(c1, s) \<Rightarrow> t1" "(c2,s) \<Rightarrow> t2" by blast
    have "\<exists>a. (IF b THEN c1 ELSE c2, s) \<Rightarrow> a"
    proof(cases "bval b s")
      case True
      from this 1 have "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t1" by blast
      then show ?thesis by blast
    next
      case False
      from this 1 have "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t2" by blast
      then show ?thesis by blast
    qed
  }   
  then show ?case by blast
qed auto

fun AA :: "com \<Rightarrow> (vname \<times> vname) set \<Rightarrow> (vname \<times> vname) set" where
 "AA SKIP A = A" |
 "AA (x::= V y) A = insert (x,y) {(a,b). x \<noteq> a \<and> x \<noteq> b \<and> (a,b) \<in> A}" |
 "AA (x::= a) A = {(a,b). x \<noteq> a \<and> x \<noteq> b \<and> (a,b) \<in> A}" | 
 "AA (c1;;c2) A = (AA c2 (AA c1 A))" |
 "AA (IF b THEN c1 ELSE c2) A = AA c1 A \<inter> AA c2 A" |
 "AA (WHILE b DO c) A = A \<inter> AA c A"

fun gen :: "com \<Rightarrow> (vname \<times> vname) set" and kill :: "com \<Rightarrow> (vname \<times> vname) set" where
  "gen SKIP = {}" |
  "kill SKIP = {}" |
  "gen (x ::= V y) =  {(x,y)}" |
  "kill (x ::= V y) = {(x',y'). x=x' \<and> y \<noteq> y' \<or> x' \<noteq> x \<and> x = y'}" |
  "gen (x ::= a) = {}" |
  "kill (x ::= a) = {(x',y'). x = x' \<or> x = y'}" |
  "gen (c1;;c2) = (gen c1 - kill c1)  \<union> gen c2" |
  "kill (c1;;c2) = (kill c1 - gen c2) \<union> kill c2" |
  "gen (IF b THEN c1 ELSE c2) = gen c1 \<inter> gen c2" |
  "kill (IF b THEN c1 ELSE c2) = kill c1 \<union> kill c2" |
  "gen (WHILE b DO c) = {}" |
  "kill (WHILE b DO c) = kill c" 

lemma assign_case: "AA (x1 ::= x2) A = A \<union> gen (x1 ::= x2) - kill (x1 ::= x2)"
proof(cases "x2")
  case (V x2)
  then show ?thesis 
  proof(cases "x1 = x2")
    case True
    from V True show ?thesis  by auto 
  next
    case False
    from V False show ?thesis by auto
  qed
qed auto


theorem AA_gen_kill: "AA c A = (A \<union> gen c) - kill c"
  apply(induction c arbitrary: A)
  by(simp,metis assign_case,auto)
  
lemma AA_distr: "AA c (A1 \<inter> A2) = AA c A1 \<inter> AA c A2" by (auto simp: AA_gen_kill)

lemma AA_idemp: "AA c (AA c A) = AA c A" by (auto simp: AA_gen_kill)

lemma AA_monotone: "A \<subseteq> B \<Longrightarrow> AA c A \<subseteq> AA c B" by(auto simp: AA_gen_kill)

theorem AA_sound:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> \<forall> (x,y) \<in> A. s x = s y \<Longrightarrow> 
   \<forall> (x,y) \<in> AA c A. s' x = s' y"
proof(induction arbitrary: A rule: big_step_induct)
  case (Assign x1 a s)
  then show ?case  by (cases "a",cases,auto)
next
  case Seq then show ?case by fastforce
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue.prems WhileTrue.IH(1) 
  have "\<forall>a\<in>AA c A. case a of (x, y) \<Rightarrow> s\<^sub>2 x = s\<^sub>2 y" by simp
  from this WhileTrue.IH(2) 
  have "\<forall>a\<in>AA (WHILE b DO c) (AA c A). case a of (x, y) \<Rightarrow> s\<^sub>3 x = s\<^sub>3 y" by simp
  then show ?case by(simp add: AA_idemp)
qed auto

fun subst :: "(vname \<Rightarrow> vname) \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst f (N n) = N n" |
  "subst f (V y) = V (f y)" |
  "subst f (Plus a1 a2) = Plus (subst f a1) (subst f a2)"

lemma subst_lemma: "aval (subst \<sigma> a) s = aval a (\<lambda>x. s (\<sigma> x))"
proof(induction a)
  case (V x) then show ?case by simp
next
  case (Plus a1 a2) then show ?case by simp 
qed auto
  

definition
  "to_map A x = (if \<exists> y. (x, y) \<in> A then SOME y. (x, y) \<in> A else x)"

fun CP where
  "CP SKIP A = SKIP"
| "CP (x ::= a) A = (x ::= subst (to_map A) a)"
| "CP (c1;;c2) A = (CP c1 A);;(CP c2 (AA c1 A))"
| "CP (IF b THEN c1 ELSE c2) A = IF b THEN CP c1 A ELSE CP c2 A"
| "CP (WHILE b DO c) A = (WHILE b DO CP c (AA (WHILE b DO c) A))"

lemma CP_skip: "CP c A = SKIP \<Longrightarrow> c = SKIP" by(induction c, auto)
lemma CP_assign: "CP c A = (x::=a) \<Longrightarrow> \<exists> y b. c = (y::=b)" by(induction c,auto)
lemma CP_seq: "CP c A = c1;;c2 \<Longrightarrow> \<exists> c1' c2'. c = c1';;c2'" by(induction c,auto)
lemma CP_If: "CP c A = (IF b THEN c1 ELSE c2) \<Longrightarrow> \<exists> c1' c2'. c = IF b THEN c1' ELSE c2'" by(induction c,auto)
lemma CP_While: "CP c A = (WHILE b DO c'') \<Longrightarrow> \<exists> c'. c = WHILE b DO c'" by(induction c,auto)

lemma to_map_eq:
  assumes "\<forall>(x,y)\<in>A. s x = s y"
  shows "(\<lambda>x. s (to_map A x)) = s"
  using assms unfolding to_map_def
  by (auto del: ext intro!: ext) (metis (mono_tags, lifting) old.prod.case someI_ex)

lemma reduce_map: 
  "\<forall>a\<in>A. case a of (x, y) \<Rightarrow> s x = s y \<Longrightarrow> 
          aval (subst (to_map A) a) s = aval a s"
  by (simp add: to_map_eq subst_lemma)

theorem CP_correct1:
  assumes "(c, s) \<Rightarrow> t" "\<forall>(x,y)\<in>A. s x = s y"
  shows   "(CP c A, s) \<Rightarrow> t"
  using assms
proof(induction c s t arbitrary: A rule: big_step_induct)
  case (Assign x a s)
  then show ?case by (auto simp add: assign_simp reduce_map)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from AA_sound[of c\<^sub>1 s\<^sub>1 s\<^sub>2 A] Seq.hyps(1) Seq.prems have 0: "\<forall>a\<in>AA c\<^sub>1 A. case a of (x, y) \<Rightarrow> s\<^sub>2 x = s\<^sub>2 y" by auto
  from Seq have 1: "(CP c\<^sub>1 A, s\<^sub>1) \<Rightarrow> s\<^sub>2" by simp
  from "0" Seq(4)[of "(AA c\<^sub>1 A)"] have 2: "(CP c\<^sub>2 (AA c\<^sub>1 A), s\<^sub>2) \<Rightarrow> s\<^sub>3" by auto
  from "1" "2" show ?case by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue.IH(1)[of "A \<inter> AA c A"] WhileTrue.prems 
  have 0: "(CP c (A \<inter> AA c A), s\<^sub>1) \<Rightarrow> s\<^sub>2" by simp
  from AA_sound[of c s\<^sub>1 s\<^sub>2 "A \<inter> AA c A"] WhileTrue.hyps(2) WhileTrue.prems 
  have 1: "\<forall>a\<in> AA c (A \<inter> AA c A). case a of (x, y) \<Rightarrow> s\<^sub>2 x = s\<^sub>2 y" by simp  

  from AA_idemp AA_distr have 2: "AA c (A \<inter> AA c A) = AA c A" by auto

  have "\<forall>a\<in> (A \<inter> AA c A). case a of (x, y) \<Rightarrow> s\<^sub>2 x = s\<^sub>2 y" using "1" "2" by auto
  then have "(CP (WHILE b DO c) (A \<inter> AA c A), s\<^sub>2) \<Rightarrow> s\<^sub>3" using WhileTrue.IH(2) by auto
  then have "(WHILE b DO CP c (AA (WHILE b DO c) (A \<inter> AA c A)),s\<^sub>2) \<Rightarrow> s\<^sub>3" by simp
  then have "(WHILE b DO CP c (AA (WHILE b DO c) (AA (WHILE b DO c) A)),s\<^sub>2) \<Rightarrow> s\<^sub>3" by simp
  then have "(WHILE b DO CP c (AA (WHILE b DO c) A),s\<^sub>2) \<Rightarrow> s\<^sub>3" using AA_idemp by metis
  then have "(CP (WHILE b DO c) A,s\<^sub>2) \<Rightarrow> s\<^sub>3" by simp 
  from this "0" WhileTrue.hyps(1) show ?case by auto
qed auto

theorem CP_correct2:
  assumes "(CP c A, s) \<Rightarrow> t" "\<forall>(x,y)\<in>A. s x = s y"
  shows "(c, s) \<Rightarrow> t"
  using assms
proof(induction "CP c A" s t arbitrary: c A rule: big_step_induct)
  case (Skip s)
  then show ?case by (metis CP_skip big_step.Skip)
next
  case (Assign x a s)
  from Assign CP_assign show ?case
    by (smt CP.simps(2) assign_simp case_prodD case_prodI2 reduce_map)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq(5) obtain c1' c2' where 0: "c = c1';;c2'" by (metis CP_seq)
  from this Seq(5) have 1: "c\<^sub>1 = CP c1' A \<and> c\<^sub>2 = CP c2' (AA c1' A)" by auto
  from this Seq(2)[of c1' A] Seq(6) have 2: "(c1', s\<^sub>1) \<Rightarrow> s\<^sub>2" by auto
  thm AA_sound[of c1' s\<^sub>1 s\<^sub>2 A]
  from this 1 Seq(6) Seq(4)[of c2' "(AA c1' A)"] AA_sound[of c1' s\<^sub>1 s\<^sub>2 A] have 3: "(c2', s\<^sub>2) \<Rightarrow> s\<^sub>3" by simp
  from 0 2 3 show ?case by blast
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case 
    by (metis (no_types, lifting) CP.simps(4) CP_If big_step.IfTrue com.inject(3))
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case 
    by (metis (no_types, lifting) CP.simps(4) CP_If big_step.IfFalse com.inject(3))  
next
  case (WhileFalse b s c)
  then obtain c'' where "WHILE b DO c'' = CP c A" by simp
  from this CP_While[of c A b c'' ] obtain c' where "c = WHILE b DO c'" by auto
  from this WhileFalse(1) show ?case by blast
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  fix b s\<^sub>1 c s\<^sub>2 s\<^sub>3 ca A
  assume 0: "bval b s\<^sub>1"
  assume 1: "(c, s\<^sub>1) \<Rightarrow> s\<^sub>2"
  assume 2: "(\<And>ca A. c = CP ca A \<Longrightarrow> \<forall>(x, y)\<in>A. s\<^sub>1 x = s\<^sub>1 y \<Longrightarrow> (ca, s\<^sub>1) \<Rightarrow> s\<^sub>2)"
  assume 3: "(WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3" 
  assume 4: "(\<And>ca A. WHILE b DO c = CP ca A \<Longrightarrow> \<forall>(x, y)\<in>A. s\<^sub>2 x = s\<^sub>2 y \<Longrightarrow> (ca, s\<^sub>2) \<Rightarrow> s\<^sub>3)"
  assume 5: "WHILE b DO c = CP ca A"
  assume 6: "\<forall>(x, y)\<in>A. s\<^sub>1 x = s\<^sub>1 y"
  from 5 CP_While[of ca A b c] obtain c' where 7: "ca = WHILE b DO c'" by auto

  from this 5 have 8: "WHILE b DO c = CP (WHILE b DO c') A" by blast
  then have "(WHILE b DO c) = (WHILE b DO CP c' (AA (WHILE b DO c') A))" by simp
  then have 9: "c = CP c' (AA (WHILE b DO c') A)" by blast
  from this 2[of c' "(AA (WHILE b DO c') A)"] 6 have 10: "(c', s\<^sub>1) \<Rightarrow> s\<^sub>2" by simp

  from  "7" "9" AA_idemp[of ca A] have 11: "WHILE b DO c = CP ca (AA ca A)" by simp
  from "6" "10" AA_sound[of c' s\<^sub>1 s\<^sub>2 A] have 12: "\<forall>(x, y)\<in>AA c' A. s\<^sub>2 x = s\<^sub>2 y" by auto
  from  "7" 12 have 13: "\<forall>(x, y)\<in>AA ca A. s\<^sub>2 x = s\<^sub>2 y" by simp
  from "4"[of ca "(AA ca A)"]  11 13 have "(ca,s\<^sub>2) \<Rightarrow> s\<^sub>3" by blast

  from this 8 10 show "(ca, s\<^sub>1) \<Rightarrow> s\<^sub>3" using "0" "7" by blast
qed 

corollary CP_correct:
  "c \<sim> CP c {}"
  apply (rule equivI)
   apply (erule CP_correct1, simp)
  apply (erule CP_correct2, simp)
  done

end