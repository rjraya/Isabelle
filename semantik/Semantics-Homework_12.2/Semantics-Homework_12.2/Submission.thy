theory Submission
  imports Defs
begin

fun cnv_i_to_abs :: "instr \<Rightarrow> int \<Rightarrow> instr" where
"cnv_i_to_abs (JMP n) i = (JMP (n+i+1))" |
"cnv_i_to_abs (JMPLESS n) i = (JMPLESS (n+i+1))" |
"cnv_i_to_abs (JMPGE n) i = (JMPGE (n+i+1))" |
"cnv_i_to_abs instr i = instr"

fun convert :: "instr list \<Rightarrow> int \<Rightarrow> instr list" where
"convert [] i = []" |
"convert (it#its) i = (cnv_i_to_abs it i) # convert its (i+1)"

lemma convert_size: "size (convert P i) = size P"
proof(induction P arbitrary: i)
  case Nil then show ?case by simp
next
  case (Cons a P) then show ?case by simp
qed

lemma convert_index: "0 \<le> (i::int) \<and> i < length P \<Longrightarrow> (convert P j) !! i = cnv_i_to_abs (P!!i) (i+j)"
proof(induction P arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons a P)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis by simp 
  next
    case False
    then have 0: "(convert (a # P) j !! i) = convert P (j+1) !! (i-1)" 
      using False int_ops(6) by auto
    from Cons(1)[of "i-1" "j+1"] have 1: "... = cnv_i_to_abs (P !! (i - 1)) ((i - 1) + (j + 1))" 
      using Cons.prems False by fastforce
    have 2: "... = cnv_i_to_abs ((a # P) !! i) (i + j)" 
      using False int_ops(6) by auto
     show ?thesis using "0" "1" "2" by auto 
   qed
qed


definition cnv_to_abs :: "instr list \<Rightarrow> instr list" where
  "cnv_to_abs P = convert P (0::int)" 

lemma cnv_size: "size (cnv_to_abs P) = size P" unfolding cnv_to_abs_def by (simp add: convert_size)

lemma cnv_index: "0 \<le> (i::int) \<and> i < length P \<Longrightarrow> (cnv_to_abs P) !! i = cnv_i_to_abs (P!!i) (i)"
  unfolding cnv_to_abs_def by(simp add: convert_index)

fun abs_iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
"abs_iexec (JMP n) (i,s,stk) = (n,s,stk)" |
"abs_iexec (JMPLESS n) (i,s,stk) = (if hd2 stk < hd stk then n else i+1,s,tl2 stk)" |
"abs_iexec (JMPGE n) (i,s,stk) = (if hd2 stk >= hd stk then n else i+1,s,tl2 stk)" |
"abs_iexec instr c = iexec instr c"

definition
  abs_exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
     ("(_/ \<turnstile>\<^sub>a (_ \<rightarrow>/ _))" [59,0,59] 60) 
where
  "P \<turnstile>\<^sub>a c \<rightarrow> c' = 
  (\<exists>i s stk. c = (i,s,stk) \<and> c' = abs_iexec (P!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < size P)"

lemma one_step1:
  assumes "cnv_to_abs P \<turnstile>\<^sub>a c \<rightarrow> c'"
  shows "P \<turnstile> c \<rightarrow> c'"
proof -
  from assms obtain i s stk where 
    0: "c = (i,s,stk) \<and> 
     c' = abs_iexec ((cnv_to_abs P)!!i) (i,s,stk) \<and> 
     0 \<le> i \<and> i < size (cnv_to_abs P)"
    using abs_exec1_def by blast
  then have bounds: "0 \<le> i \<and> i < size P" by (simp add: cnv_size)
  have equiv: "abs_iexec ((cnv_to_abs P)!!i) (i,s,stk) = iexec(P!!i) (i,s,stk)"
    by(cases "P!!i")(auto simp add: bounds cnv_index)
  from "0" bounds equiv show ?thesis by (simp add: exec1I)
qed

lemma one_step2:
  assumes "P \<turnstile> c \<rightarrow> c'"
  shows "cnv_to_abs P \<turnstile>\<^sub>a c \<rightarrow> c'"
proof -
  from assms obtain i s stk where 
    0: "c = (i,s,stk) \<and> 
        c' = iexec (P!!i) (i,s,stk) \<and> 
        0 \<le> i \<and> i < size P"
    using exec1_def by blast
  then have bounds: "0 \<le> i \<and> i < size P" by simp 
  have equiv: "abs_iexec ((cnv_to_abs P)!!i) (i,s,stk) = iexec(P!!i) (i,s,stk)"
    by(cases "P!!i")(auto simp add: bounds cnv_index)
  from "0" bounds equiv show ?thesis
    by (simp add: abs_exec1_def cnv_size)
qed

abbreviation 
  exec_abs :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile>\<^sub>a (_ \<rightarrow>*/ _))" 50)
where
  "exec_abs P c c' \<equiv> star (abs_exec1 P) c c'"

theorem cnv_to_abs_correct: "cnv_to_abs P \<turnstile>\<^sub>a c \<rightarrow>* c' \<longleftrightarrow> P \<turnstile> c \<rightarrow>* c'"
  apply(rule iffI)
  apply(induction rule: star.induct,simp,meson one_step1 star.step)
  apply(induction rule: star.induct,simp,meson one_step2 star.step)
  done

fun cnv_i_to_rel :: "instr \<Rightarrow> int \<Rightarrow> instr" where
"cnv_i_to_rel (JMP n) i = (JMP (n-i-1))" |
"cnv_i_to_rel (JMPLESS n) i = (JMPLESS (n-i-1))" |
"cnv_i_to_rel (JMPGE n) i = (JMPGE (n-i-1))" |
"cnv_i_to_rel instr i = instr"

lemma inv_i: "(cnv_i_to_abs (cnv_i_to_rel instr i) i) = instr"
  by(induction instr,auto)

fun convertr :: "instr list \<Rightarrow> int \<Rightarrow> instr list" where
"convertr [] i = []" |
"convertr (it#its) i = (cnv_i_to_rel it i) # convertr its (i+1)"

lemma inv_c: "(convert (convertr P i) i) = P"
  by(induction P arbitrary: i,simp,simp add: inv_i)

definition cnv_to_rel :: "instr list \<Rightarrow> instr list" where
  "cnv_to_rel P =  convertr P (0::int)"

lemma inv_p: "cnv_to_abs (cnv_to_rel P) = P"
  unfolding cnv_to_abs_def cnv_to_rel_def by (simp add: inv_c)

theorem cnv_to_rel_correct:
  "P \<turnstile>\<^sub>a c \<rightarrow>* c' \<longleftrightarrow> cnv_to_rel P \<turnstile> c \<rightarrow>* c'"
  by (metis cnv_to_abs_correct inv_p)

end