theory MyWellfounded
  imports HOL.Transitive_Closure Main 
begin

definition wf :: "('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "wf r A \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

definition wfP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "wfP r A \<longleftrightarrow> wf {(x, y). r x y} A"

lemma wfP_wf_eq [pred_set_conv]: 
  "wfP (\<lambda> x y. (x, y) \<in> r) A = wf r A" by (auto simp add: wfP_def wf_def)
 
lemma wfUNIVI: "(\<And> P. \<forall> z \<in> A.( (\<forall>x \<in> A. (\<forall>y \<in> A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> P z)) \<Longrightarrow> wf r A"
  unfolding wf_def by blast                     

lemmas wfPUNIVI = wfUNIVI [to_pred]

lemma wf_induct:
  assumes 0: "wf r A"
  assumes 1: "(\<forall>x \<in> A. (\<forall>y \<in> A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x)"
  shows "a \<in> A \<longrightarrow> P a"
  using "0" "1" wf_def by blast

lemmas wfP_induct = wf_induct [to_pred]

lemmas wf_induct_rule = wf_induct [rule_format, consumes 1, case_names less, induct set: wf]

lemmas wfP_induct_rule = wf_induct_rule [to_pred, induct set: wfP]

text \<open>Point-free characterization of well-foundedness\<close>

lemma wfE_pf: "wf R B \<Longrightarrow> A  \<subseteq> (R `` A) \<inter> B \<Longrightarrow> A  = {}"
proof -
  assume 0: "wf R B" 
  assume 1: "A \<subseteq> (R `` A) \<inter> B"
  from 1 have "A \<subseteq> {y. \<exists>x\<in>A. (x, y) \<in> R} \<inter> B" by auto
  from this have 2: "\<forall> a \<in> A. \<exists> x \<in> A. (x,a) \<in> R" by auto
  from 0 have "(\<forall>P. (\<forall>x \<in> B. (\<forall>y \<in> B. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> B. P x))"
    by (auto simp add: wf_def)
  from this have "(\<forall>x \<in> B. (\<forall>y \<in> B. (y, x) \<in> R \<longrightarrow> y \<notin> A) \<longrightarrow> x \<notin> A) \<longrightarrow> (\<forall>x \<in> B. x \<notin> A)"
    by (rule allE)
  from this 2 show ?thesis 
    by (metis "1" IntE Int_absorb1 all_not_in_conv)
qed

lemma wfI_pf:
  "(\<forall> A. A \<subseteq> (R `` A) \<inter> B \<longrightarrow> A = {}) \<Longrightarrow> wf R B"
proof(rule wfUNIVI)
  fix P :: "'a \<Rightarrow> bool"
  assume 0: "\<forall> A. A \<subseteq> (R `` A) \<inter> B \<longrightarrow> A = {}"
  show wf: "\<forall> z \<in> B.( (\<forall>x\<in>B. (\<forall>y\<in>B. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> P z)"
  proof 
   fix z
   assume 1: "z \<in> B"
   show "( (\<forall>x\<in>B. (\<forall>y\<in>B. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> P z)"
   proof 
    let ?A = "{x \<in> B. \<not> P x}"
    from 0 have 2: "?A \<subseteq> (R `` ?A) \<inter> B \<longrightarrow> ?A = {}" by blast
    assume 3: "\<forall>x \<in> B. (\<forall>y \<in> B. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x"
    show "P z"
    proof -
     from 2 3 have "?A = {}" by (smt ImageI IntI mem_Collect_eq subsetI)
     from this 1 show "P z" by blast
    qed
   qed
 qed
qed

lemma wf_pf: "wf R B \<longleftrightarrow> (\<forall> A. A  \<subseteq> (R `` A) \<inter> B \<longrightarrow> A  = {})"
  by (meson MyWellfounded.wfE_pf MyWellfounded.wfI_pf)

lemma restrict_wf: "wf R A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> wf R B"
  by (simp add: dual_order.trans le_infI wf_pf)

subsubsection \<open>Minimal-element characterization of well-foundedness\<close>

lemma wf_wellorderI:
  assumes wf: "wf {(x::'a::ord, y). x < y} UNIV"
    and lin: "OFCLASS('a::ord, linorder_class)"
  shows "OFCLASS('a::ord, wellorder_class)"
  using lin
  apply (rule wellorder_class.intro)
  apply (rule class.wellorder_axioms.intro)
  apply (rule wf_induct_rule [OF wf])
  apply auto
  done

lemma (in wellorder) wf: "wf {(x, y). x < y} UNIV"
  unfolding wf_def by (blast intro: less_induct)

(*lemma (in wellorder) wfb: "wf {(x, y). x < y} B"
  by (meson Int_greatest UNIV_I inf.boundedE local.wf subsetI wf_pf)*)

lemma wfE_min:
  assumes wf: "wf R B" and Q: "x \<in> Q" and "Q \<subseteq> B"
  obtains z where "z \<in> Q" "\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q"
  using Q wfE_pf[OF wf, of Q]
  by (smt Image_iff IntI assms(3) equals0D subset_eq)
  
lemma wfI_min:
  assumes a: "\<And>x Q. x \<in> Q \<Longrightarrow> Q \<subseteq> B \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q"
  shows "wf R B"
proof(rule wfI_pf)
  show "\<forall>A. A \<subseteq> R `` A \<inter> B \<longrightarrow> A = {} "
  proof 
    fix A 
    show "A \<subseteq> (R `` A) \<inter> B \<longrightarrow> A = {}"
    proof
      assume b: "A \<subseteq> (R `` A) \<inter> B"
      show "A = {}"
      proof -
        have "False" if "x \<in> A" for x using a[OF that] b by blast
        then show "A = {}" by blast
      qed
    qed
  qed
qed

lemma wf_eq_minimal: "wf r B \<longleftrightarrow> (\<forall>Q x. x \<in> Q \<longrightarrow> Q \<subseteq> B \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q))"
  by (meson MyWellfounded.wfE_min MyWellfounded.wfI_min)

lemmas wfP_eq_minimal = wf_eq_minimal [to_pred]

subsection \<open>Accessible Part\<close>

text \<open>
  Inductive definition of the accessible part \<open>acc r\<close> of a
  relation; see also @{cite "paulin-tlca"}.
\<close>

inductive_set acc :: "('a \<times> 'a) set \<Rightarrow> 'a set" for r :: "('a \<times> 'a) set"
  where accI: "(\<And>y. (y, x) \<in> r \<Longrightarrow> y \<in> acc r) \<Longrightarrow> x \<in> acc r"

abbreviation termip :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "termip r \<equiv> accp (r\<inverse>\<inverse>)"

abbreviation termi :: "('a \<times> 'a) set \<Rightarrow> 'a set"
  where "termi r \<equiv> acc (r\<inverse>)"

lemmas accpI = accp.accI

lemma accp_eq_acc [code]: "accp r = (\<lambda>x. x \<in> acc {(x, y). r x y})"
  by (simp add: acc_def)

text \<open>Induction rules\<close>

theorem accp_induct:
  assumes major: "accp r a"
  assumes hyp: "\<And>x. accp r x \<Longrightarrow> \<forall>y. r y x \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  apply (rule major [THEN accp.induct])
  apply (rule hyp)
   apply (rule accp.accI)
   apply auto
  done

lemmas accp_induct_rule = accp_induct [rule_format, induct set: accp]

theorem accp_downward: "accp r b \<Longrightarrow> r a b \<Longrightarrow> accp r a"
  by (cases rule: accp.cases)

lemma accp_downwards_aux: "r\<^sup>*\<^sup>* b a \<Longrightarrow> accp r a \<longrightarrow> accp r b"
  by (erule rtranclp_induct) (blast dest: accp_downward)+

theorem accp_downwards: "accp r a \<Longrightarrow> r\<^sup>*\<^sup>* b a \<Longrightarrow> accp r b"
  by (blast dest: accp_downwards_aux)

theorem accp_wfPD: "wfP r {e. r\<^sup>*\<^sup>* s e } \<Longrightarrow> accp r s"
  apply (erule wfP_induct_rule)
  apply(auto)

  done

theorem accp_wfPI: "\<forall>x. accp r x \<Longrightarrow> wfP r {e. r\<^sup>*\<^sup>* x e} "
  apply (rule wfPUNIVI)
  apply (rule_tac P = P in accp_induct)
   apply blast+
  done

theorem accp_wfPD: "wfP r \<Longrightarrow> accp r x"
  apply (erule wfP_induct_rule)
  apply (rule accp.accI)
  apply blast
  done

theorem wfP_accp_iff: "wfP r = (\<forall>x. accp r x)"
  by (blast intro: accp_wfPI dest: accp_wfPD)


end