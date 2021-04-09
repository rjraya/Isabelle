theory Verified
  imports Wp Wlp 
begin

section \<open>Introduction rules for if and do\<close>

 lemma wlp_ifI: 
  assumes "\<forall> b c. ((b,c) \<in> set gcs \<and> bval b s) \<longrightarrow> P s \<longrightarrow> wlp c Q s"
  shows "P s \<Longrightarrow> BB gcs s \<Longrightarrow>  wlp (IF gcs FI) Q s"
   using assms by (simp add: wlp_if_eq)

 lemma wp_ifI: 
   assumes "\<forall> b c. ((b,c) \<in> set gcs \<and> bval b s) \<longrightarrow> P s \<longrightarrow> wp c Q s"
   assumes "P s"
   assumes "BB gcs s"
   shows "wp (IF gcs FI) Q s"
   using assms by (simp add: wp_if_eq)

text \<open>
 The proof is completely analogous to the one we had in IMP. Dijkstra gives other
 characterizations but we find them intuitively equivalent to this one and less practical
 to use, at least in Isabelle.
\<close>

lemma wp_doI:
  assumes WF: "wf R"
  assumes INIT: "I s\<^sub>0" 
  assumes STEP: "\<And> s. \<lbrakk>I s; BB gcs s \<rbrakk> \<Longrightarrow> wp (IF gcs FI) (\<lambda> s'. I s' \<and>  (s',s) \<in> R) s "
  assumes FINAL: "\<And> s. \<lbrakk>I s; \<not> BB gcs s \<rbrakk> \<Longrightarrow> Q s"
  shows "wp (DO gcs OD) Q s\<^sub>0"
  using WF INIT
  proof induction
    case (less s) 
    show ?case
    proof (rule wp_do_unfold[THEN iffD2])
      show "if BB gcs s then wp (IF gcs FI) (wp (DO gcs OD) Q) s else Q s" 
      proof (split if_split; intro allI impI conjI)
        assume [simp]: "BB gcs s"
        
        from STEP \<open>I s\<close> have "wp (IF gcs FI) (\<lambda>s'. I s' \<and> (s',s)\<in>R) s" by simp
        thus "wp (IF gcs FI) (wp (DO gcs OD) Q) s" proof (rule post_strengthen)
          fix s' assume "I s' \<and> (s',s)\<in>R"
          with less.IH show "wp (DO gcs OD) Q s'" by blast
        qed
      next
        assume [simp]: "\<not> BB gcs s"
        from STEP \<open>I s\<close> show "Q s" by (simp add: FINAL)
      qed
    qed
  qed

section \<open>Verification of Max and GCD functions\<close>

text\<open>
 Here we prove correct a program to find the maximum of two numbers (Max) and
 a program to compute the greatest common divisor of two numbers (GCD). It could
 be interesting to extend our formalization with a proper vcg generator.  
\<close>

subsection \<open>Max function\<close>

definition geq: "GreaterEq a b = Cmpop (\<lambda> a b. a \<ge> b) a b"

definition Max :: "com" where
"Max = IF [(GreaterEq (V ''x'')  (V ''y''),''m'' ::= (V ''x'')),
           (GreaterEq (V ''y'') (V ''x''),''m'' ::= (V ''y''))] FI"

lemma max_correct: "
 a = s ''x'' \<and> b = s ''y'' \<Longrightarrow>
 wp Max (\<lambda> s. s ''m'' = max a b \<and> a = s ''x'' \<and> b = s ''y'') s 
"
proof -
  assume 0: "a = s ''x'' \<and> b = s ''y''"
  let ?gcs = "[(GreaterEq (V ''x'') (V ''y''), ''m'' ::= V ''x''),
               (GreaterEq (V ''y'') (V ''x''), ''m'' ::= V ''y'')]"
  let ?Q = "(\<lambda>s. s ''m'' = max a b \<and> a = s ''x'' \<and> b = s ''y'')"
  have 1: "BB ?gcs s" unfolding BB_def geq by (simp; metis bval.simps(4) le_cases)

  have 2: "\<And> b' c'. ((b',c') \<in> set ?gcs \<and> bval b' s)  \<Longrightarrow>
               wp c' (\<lambda>s. s ''m'' = max a b \<and> a = s ''x'' \<and> b = s ''y'') s"
  proof - 
    fix b' c'
    assume 3: "(b',c') \<in> set ?gcs \<and> bval b' s"
    show "wp c' (\<lambda>s. s ''m'' = max a b \<and> a = s ''x'' \<and> b = s ''y'') s"
    proof -
      {assume "b' = (GreaterEq (V ''x'') (V ''y'')) \<and> c' = (''m'' ::= V ''x'')"
      then have "wp c' ?Q s"
        using "0" "3" geq by (simp; subst wp_assign_eq; auto)}
    note case1 = this
      {assume "b' = (GreaterEq (V ''y'') (V ''x'')) \<and> c' = (''m'' ::= V ''y'')"
      then have "wp c' ?Q s"
        using "0" "3" geq by (simp; subst wp_assign_eq; auto)}
    note case2 = this
    from "3" case1 case2 show ?thesis by auto
    qed
  qed

  show ?thesis by (simp add: "1" "2" Max_def wp_ifI)
qed

subsection \<open>GCD function\<close>

definition gr: "Greater a b = Cmpop (\<lambda> a b. a > b) a b"

definition minus: "Minus a b = Binop (\<lambda> a b. a - b) a b"

definition Gcd :: "com" where
"Gcd = DO [(Greater (V ''x'') (V ''y''),''x'' ::= Minus (V ''x'') (V ''y'')),
           (Greater (V ''y'') (V ''x''),''y'' ::= Minus (V ''y'') (V ''x''))] OD"


lemma gcd_correct: "
 a > 0 \<and> b > 0 \<Longrightarrow>
 a = s\<^sub>0 ''x'' \<and> b = s\<^sub>0 ''y'' \<Longrightarrow>
 wp Gcd (\<lambda> s. s ''x'' = gcd a b) s\<^sub>0 
"
proof -
  let ?I = "\<lambda> s. gcd a b = gcd (s ''x'') (s ''y'') \<and> s ''x'' > 0 \<and> s ''y'' > 0"
  let ?R = "measure (\<lambda>s.  nat (s ''x'') + nat (s ''y''))"
  let ?gcs = "
        [(Greater (V ''x'') (V ''y''),''x'' ::= Minus (V ''x'') (V ''y'')),
         (Greater (V ''y'') (V ''x''),''y'' ::= Minus (V ''y'') (V ''x''))] 
  "
  let ?Q = "(\<lambda> s. s ''x'' = gcd a b)"
  
  assume 0: "a > 0 \<and> b > 0"
  assume 1: "a = s\<^sub>0 ''x'' \<and> b = s\<^sub>0 ''y''"
  have 2: "wf ?R" by simp
  from "0" "1" have 3: "?I s\<^sub>0" by blast
  have 4: "(\<And>s. ?I s \<Longrightarrow> \<not> BB ?gcs s \<Longrightarrow> ?Q s)" 
    using BB_def gr minus
    by (smt aval.simps(2) bval.simps(4) gcd_idem_int list.set_intros(1) set_rev_mp set_subset_Cons)


  {fix s
  assume 0: "?I s" 
  assume 1: "BB ?gcs s"
  
  have "wp (IF ?gcs FI) (\<lambda>s'. ?I s' \<and> (s', s) \<in> ?R) s"
  proof(subst wp_if_eq, simp, rule conjI,simp add: "1"; intro allI impI) 
    show "\<And> ba c.
       (ba = Greater (V ''x'') (V ''y'') \<and> c = ''x'' ::= Minus (V ''x'') (V ''y'') \<or>
        ba = Greater (V ''y'') (V ''x'') \<and> c = ''y'' ::= Minus (V ''y'') (V ''x'')) \<and>
       bval ba s \<Longrightarrow>
       wp c
        (\<lambda>s'. gcd a b = gcd (s' ''x'') (s' ''y'') \<and>
              0 < s' ''x'' \<and>
              0 < s' ''y'' \<and>
              nat (s' ''x'') + nat (s' ''y'') < nat (s ''x'') + nat (s ''y''))
        s"
    proof -
      fix ba c
      assume 2:"
        (ba = Greater (V ''x'') (V ''y'') \<and> c = ''x'' ::= Minus (V ''x'') (V ''y'') \<or>
        ba = Greater (V ''y'') (V ''x'') \<and> c = ''y'' ::= Minus (V ''y'') (V ''x'')) \<and>
        bval ba s
      "
      show "wp c
        (\<lambda>s'. gcd a b = gcd (s' ''x'') (s' ''y'') \<and>
              0 < s' ''x'' \<and>
              0 < s' ''y'' \<and>
              nat (s' ''x'') + nat (s' ''y'') < nat (s ''x'') + nat (s ''y''))
        s "
      proof(cases "bval (Greater (V ''x'') (V ''y'')) s")
        case True
        then have "c = ''x'' ::= Minus (V ''x'') (V ''y'')" 
          using "2" gr by auto
        then show ?thesis 
          apply(simp,subst wp_assign_eq,simp,intro conjI)
          apply (simp add: "0" gcd_diff1 minus)
          using True gr minus apply auto[1]
          by (simp add: "0",simp add: "0",simp add: "0" minus)
      next
        case False
        then have "c = ''y'' ::= Minus (V ''y'') (V ''x'')" 
          using "2" by blast
        then show ?thesis 
          apply(simp,subst wp_assign_eq,simp,intro conjI)
          apply (metis "0" aval.simps(2) aval.simps(4) gcd.commute gcd_diff1 minus)
          apply (simp add: "0")
          using "2" gr minus apply auto[1]
          by(simp add: "0",simp add: "0" minus)
        qed
      qed
    qed}
  then have 5: "(\<And>s. ?I s \<Longrightarrow> BB ?gcs s \<Longrightarrow> wp (IF ?gcs FI) (\<lambda>s'. ?I s' \<and> (s', s) \<in> ?R) s)"
    by blast

  from "2" "3" "4" "5" wp_doI[of ?R ?I s\<^sub>0 ?gcs ?Q] have "
    wp (DO ?gcs OD) ?Q s\<^sub>0
  "  by blast
  then show ?thesis 
    by (simp add: Gcd_def)
qed
  

end