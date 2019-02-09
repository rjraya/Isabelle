theory Ex14
  imports "IMP.Small_Step" "IMP.Live"
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
  apply(induction rule: star_induct,simp)
  using small_step_confinement vars_subsetD 
  by (metis DiffD2 DiffI UNIV_I subsetCE )

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
  
  
  
thm star_induct
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
  {
    fix c1 c2 s t
    assume A: "(c1;;c2,s) \<rightarrow>* (SKIP,t)" and vars: "vars c1 \<inter> vars c2 = {}"
    thm small_steps_indep small_steps_confinement small_steps_SeqE seq_comp
    from A(1) small_steps_SeqE[of c1 c2 s t] obtain s1 where 
     c1: "(c1, s) \<rightarrow>* (SKIP, s1)" and c2: "(c2, s1) \<rightarrow>* (SKIP, t)" by blast
    from small_steps_confinement[OF c2] small_steps_confinement[OF c1]
      have s1_t: "s1 = t on UNIV -vars c2" and s1_s: "s = s1 on UNIV -vars c1" 
      by auto
    from small_steps_indep[OF c2 s1_s] A(1) obtain t1 where
      step1: "(c2,s) \<rightarrow>* (SKIP,t1)" "t = t1 on UNIV - vars c1" sorry
   

    from this seq_comp[of c2 t' t c1]
    have "(c2;;c1,s) \<rightarrow>* (SKIP,t)" 
    proof -

    qed
  } with vars show ?thesis unfolding equiv_com_def by (metis Int_commute)
qed

end