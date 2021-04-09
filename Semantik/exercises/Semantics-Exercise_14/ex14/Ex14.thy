theory Ex14
  imports "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/Small_Step"
          "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/Live"
begin

lemma [simp]: "s1 = s2 on X \<Longrightarrow> vars a \<subseteq> X \<Longrightarrow> aval a s1 = aval a s2"
  by(induction a,auto)
(* also find theorems aval ... *)
lemma [simp]: "s1 = s2 on X \<Longrightarrow> vars b \<subseteq> X \<Longrightarrow> bval b s1 = bval b s2"
  by(induction b,auto)

lemma vars_subsetD[dest]: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> vars c' \<subseteq> vars c"
  by(induction rule: small_step_induct,auto) 

lemma small_step_confinement: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> s = s' on UNIV - vars c"
  by(induction rule: small_step_induct,auto) 

lemma small_steps_confinement: "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> s = s' on UNIV - vars c"
proof(induction rule: star_induct)
  case (step c s c' s1) 
  from small_step_confinement[of c s c' s1] step.hyps(1)
  have 1: "s = s1 on UNIV - vars c" by simp
  from vars_subsetD[of c s c' s1] step.IH step.hyps(1)
  have 2: "s1 = s' on UNIV - vars c" by blast
  from 1 2 show ?case by auto
qed simp

lemma small_step_indep:
 "(c,s) \<rightarrow> (c',s') \<Longrightarrow> s = t on X \<Longrightarrow> vars c \<subseteq> X \<Longrightarrow> 
  \<exists> t'. (c,t) \<rightarrow> (c',t') \<and> s' = t' on X"
  by(induction rule: small_step_induct,auto)

lemma small_steps_indep: 
 "\<lbrakk>(c,s) \<rightarrow>* (c',s'); s = t on X; vars c \<subseteq> X\<rbrakk> \<Longrightarrow>
  (\<exists> t'. (c,t) \<rightarrow>* (c',t') \<and> s' = t' on X)"
proof(induction arbitrary: t rule: star_induct)
case refl
  then show ?case by blast
next
  case (step c s c1 s1)
  from small_step_indep[OF step(1) step.prems] 
  obtain t1 where t1: "(c,t) \<rightarrow> (c1,t1)" "s1 = t1 on X" by blast (* difficult! *)
  moreover have "vars c1 \<subseteq> X" 
    using \<open>vars c \<subseteq> X\<close> step(1) by auto
  ultimately obtain t' where "(c1,t1) \<rightarrow>* (c',t')" "s' = t' on X" using step.IH[of t1]
    by auto
  with \<open>(c,t) \<rightarrow> (c1,t1)\<close>  show ?case by(blast intro: star_step)
qed
  
lemma small_steps_SeqE: 
 "(c1;;c2,s) \<rightarrow>* (SKIP,s') \<Longrightarrow> 
  \<exists> t. (c1,s) \<rightarrow>* (SKIP,t) \<and> (c2,t) \<rightarrow>* (SKIP,s')"
  by (induction "c1;;c2" s arbitrary: c1 c2 rule: star_induct)
     (blast intro: star_step)

thm seq_comp

definition equiv_com :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>\<^sub>s" 50) where
 "c1 \<sim>\<^sub>s c2 \<longleftrightarrow> (\<forall> s t. (c1,s) \<rightarrow>* (SKIP,t) \<longleftrightarrow> (c2,s) \<rightarrow>* (SKIP,t))"

lemma ec_refl[simp]: "equiv_com c c" using equiv_com_def by simp
lemma ec_sym: "equiv_com c1 c2 \<longleftrightarrow> equiv_com c2 c1" using equiv_com_def by auto
lemma ec_trans[trans]: "equiv_com c1 c2 \<Longrightarrow> equiv_com c2 c3 \<Longrightarrow> equiv_com c1 c3" 
  using equiv_com_def by auto

lemma "c1 \<sim>\<^sub>s c2 \<longleftrightarrow> c1 \<sim> c2" unfolding equiv_com_def equiv_c_def by(metis big_iff_small)

theorem Seq_equiv_Seq_reorder:
  assumes vars: "vars c1 \<inter> vars c2 = {}"
  shows "(c1 ;; c2) \<sim>\<^sub>s (c2 ;; c1)" 
proof -
  { fix s t and c1 c2 :: com
    assume A: "vars c1 \<inter> vars c2 = {}" "(c1 ;; c2, s) \<rightarrow>* (SKIP, t)"
    from small_steps_SeqE[OF A(2)] obtain s1 where
      c1: "(c1, s) \<rightarrow>* (SKIP, s1)" and c2: "(c2, s1) \<rightarrow>* (SKIP, t)"
      by blast
    from small_steps_confinement[OF c2] small_steps_confinement[OF c1] have
      "s1 = t on UNIV - vars c2" and s1_s: "s1 = s on UNIV - vars c1"
      by auto
    from small_steps_indep[OF c2 s1_s] A(1) obtain t1 where
      step1: "(c2, s) \<rightarrow>* (SKIP, t1)" "t = t1 on UNIV - vars c1"
      by blast
    from small_steps_confinement[OF step1(1)] have "s = t1 on UNIV - vars c2" .
    from small_steps_indep[OF c1 this] A(1) obtain t' where
      step2: "(c1, t1) \<rightarrow>* (SKIP, t')" "s1 = t' on UNIV - vars c2"
      by blast
    from small_steps_confinement[OF step2(1)] have "t1 = t' on UNIV - vars c1" .
    from seq_comp[OF step1(1) step2(1)] have steps: "(c2 ;; c1, s) \<rightarrow>* (SKIP, t')" .
    moreover have "t' = t"
      using \<open>t1 = t' on UNIV - vars c1\<close> \<open>t = t1 on UNIV - vars c1\<close>
      using \<open>s1 = t' on UNIV - vars c2\<close> \<open>s1 = t on UNIV - vars c2\<close>
      using \<open>vars c1 \<inter> vars c2 = {}\<close>
      by(simp add: set_eq_iff) (metis DiffI ext iso_tuple_UNIV_I)
    ultimately have "(c2 ;; c1, s) \<rightarrow>* (SKIP, t)"
      by simp
  } note * = this
  from *[of c1 c2] *[of c2 c1] show ?thesis
    using vars unfolding equiv_com_def by blast
qed

end