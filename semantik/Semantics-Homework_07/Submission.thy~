theory Submission
  imports Defs
begin

program_spec factorial_prog
  assumes "n \<ge> 0" ensures "a = factorial n\<^sub>0"
  defines \<open>
    a = 1;
    i = 1;
    while (i \<le> n)
      @variant\<open>nat (n+1 - i)\<close>
      @invariant\<open> n+1 \<ge> i \<and> i \<ge> 1 \<and> n = n\<^sub>0 \<and> 
                  (if i = n+1 then a = factorial n 
                   else a = factorial (i-1))  :: bool\<close>
    {
      a = a * i;
      i = i + 1
    }
  \<close>
  apply vcg_cs
  done

program_spec fib_prog
  assumes "n \<ge> 0" ensures "a = fib n"
  defines \<open>
    a = 0; b = 1;
    i = 0;
    while (i < n) 
      @variant\<open>nat (n-i)\<close>
      @invariant\<open>a \<ge> 0 \<and> b \<ge> 1 \<and> n = n\<^sub>0 \<and> i \<ge> 0 \<and> i \<le> n \<and>
                 a = fib(i) \<and> b = fib(i+1) :: bool\<close>   
    {
      c = b;
      b = a + b;
      a = c;
      i = i + 1
    }
  \<close>
  apply vcg_cs
  apply (simp add: add.commute)
  done


program_spec fib_prog'
  assumes True ensures "a = fib n\<^sub>0"
  defines \<open>
    a = 0; b = 1;
    i = 0;
    while (i < n) 
      @variant\<open>nat (n-i)\<close>
      @invariant\<open>a \<ge> 0 \<and> b \<ge> 1 \<and> n = n\<^sub>0 \<and> i \<ge> 0  \<and> (n\<^sub>0 < i \<longrightarrow> i = 0) \<and>
                 a = fib(i) \<and> b = fib(1+i) :: bool\<close>
    {
      c = b;
      b = a + b;
      a = c;
      i = i + 1
    }
  \<close>
  apply vcg_cs
   apply (simp add: add.commute)
  by auto


fun lhsv :: "com \<Rightarrow> vname set" where
  "lhsv (Assign vn ae) = {vn}"
| "lhsv SKIP = {}"
| "lhsv (c;;cs) = lhsv c \<union> lhsv cs"
| "lhsv (IF b THEN c1 ELSE c2) = lhsv c1 \<union> lhsv c2"
| "lhsv (WHILE b DO c) = lhsv c"

lemma step_modset: "(c,s) \<Rightarrow> s' \<Longrightarrow> (\<forall> x. x \<notin> lhsv c \<longrightarrow> s' x = s x)"
  by(induction c s s' rule: big_step_induct; auto)

theorem wp_strengthen_modset:
  "wp c Q s \<Longrightarrow> wp c (\<lambda>s'. Q s' \<and> (\<forall>x. x\<notin>lhsv c \<longrightarrow> s' x = s x)) s"
  using step_modset wp_def by auto

end