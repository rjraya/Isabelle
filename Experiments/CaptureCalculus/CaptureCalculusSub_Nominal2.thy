theory CaptureCalculusSub_Nominal2
  imports "Nominal2.Nominal2" 
          "HOL-Library.Rewrite"
          "HOL-Library.FSet"
          "HOL-Library.Product_Lexorder"
          "HOL-Eisbach.Eisbach" 
begin

text\<open>Authors: Martin Odersky with contributions of his team.
     Formalization: Rodrigo Raya.\<close>

section \<open>Basic definitions\<close>

subsection \<open>Types and terms\<close>

no_syntax
  "_Map" :: "maplets => 'a \<rightharpoonup> 'b"  ("(1[_])")

atom_decl vrs

nominal_datatype ty = 
    Tvar   "vrs"
  | Top
  | Arrow x::vrs S::"ty" T::"ty" binds x in S T
  | Forall x::vrs T::"ty" B::"ty" binds x in T
  | CapSet "vrs list" "ty"

nominal_datatype trm = 
    Var   "vrs"
  | Abs   x::"vrs" t::"trm" T::"ty" binds x in t T
  | TAbs  x::"vrs" t::"trm" B::"ty" binds x in t
  | App   "trm" "trm" (infixl "\<cdot>" 200)
  | TApp  "trm" "ty"  (infixl "\<cdot>\<^sub>\<tau>" 200)

text \<open>To be polite to the eye, some more familiar notation is introduced. 
  Because of the change in the order of arguments, one needs to use 
  translation rules, instead of syntax annotations at the term-constructors
  as given above for \<^term>\<open>Arrow\<close>.\<close>

abbreviation
  Forall_syn :: "vrs \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"  ("(3\<forall>_<:_./ _)" [0, 0, 10] 10) 
where
  "\<forall>X<:T\<^sub>1. T\<^sub>2 \<equiv> Forall X T\<^sub>2 T\<^sub>1"

abbreviation
  Abs_syn    :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"  ("(3\<lambda>_:_./ _)" [0, 0, 10] 10) 
where
  "\<lambda>x:T. t \<equiv> Abs x t T"

abbreviation
  TAbs_syn   :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("(3\<lambda>_<:_./ _)" [0, 0, 10] 10) 
where
  "\<lambda>X<:T. t \<equiv> TAbs X t T"

abbreviation
  CapSet_syn   :: "vrs list \<Rightarrow> ty \<Rightarrow> ty" ("(2_ \<triangleright> _)" [0, 10] 10) 
where
  "C \<triangleright> T \<equiv> CapSet C T"

lemma fresh_vrs_list: "atom x \<sharp> L \<Longrightarrow> x \<notin> set L"
  apply(induction L)
  by(simp_all add: fresh_Nil fresh_Cons fresh_at_base)

subsection \<open>Environment\<close>

nominal_datatype binding = 
    VarB vrs ty 
  | TVarB vrs ty

type_synonym env = "binding list"

text \<open>In order to state validity-conditions for typing-contexts, the notion of
  a \<open>dom\<close> of a typing-context is handy.\<close>

nominal_function "tyvrs_of" :: "binding \<Rightarrow> vrs list"
where
  "tyvrs_of (VarB  x y) = []"
| "tyvrs_of (TVarB x y) = [x]"
  apply(auto simp add: tyvrs_of_graph_aux_def eqvt_def)
  using binding.strong_exhaust by blast

nominal_termination (eqvt)
  by lexicographic_order

nominal_function "vrs_of" :: "binding \<Rightarrow> vrs list"
where
  "vrs_of (VarB  x y) = [x]"
| "vrs_of (TVarB x y) = []"
  apply(auto simp add: vrs_of_graph_aux_def eqvt_def)
  using binding.strong_exhaust by blast

nominal_termination (eqvt)
  by lexicographic_order

primrec "ty_dom" :: "env \<Rightarrow> vrs list"
where
  "ty_dom [] = []"
| "ty_dom (X#\<Gamma>) = (tyvrs_of X) @ (ty_dom \<Gamma>)" 

lemma ty_dom_eqvt [eqvt]:
  shows "p \<bullet> (ty_dom E) =ty_dom (p \<bullet> E)"
proof(induct E)
  case (Cons a l)
  show ?case
    apply(rule binding.strong_exhaust[of a])
    using Cons by auto
qed auto

primrec "trm_dom" :: "env \<Rightarrow> vrs list"
where
  "trm_dom [] = []"
| "trm_dom (X#\<Gamma>) = (vrs_of X) @ (trm_dom \<Gamma>)" 

lemma trm_dom_eqvt [eqvt]:
  shows "p \<bullet> (trm_dom E) = trm_dom (p \<bullet> E)"
proof(induct E)
  case (Cons a l)
  show ?case
    apply(rule binding.strong_exhaust[of a])
    using Cons by auto
qed auto

lemma doms_append:
  shows "ty_dom (\<Gamma>@\<Delta>) = ((ty_dom \<Gamma>) @ (ty_dom \<Delta>))"
  and   "trm_dom (\<Gamma>@\<Delta>) = ((trm_dom \<Gamma>) @ (trm_dom \<Delta>))"
  by (induct \<Gamma>) (auto)

lemma ty_dom_supp:
  shows "(supp (ty_dom  \<Gamma>)) = set (map atom (ty_dom \<Gamma>))"
  and   "(supp (trm_dom \<Gamma>)) = set (map atom (trm_dom \<Gamma>))"
  using supp_finite_set_at_base supp_set by auto

lemma ty_binding_existence:
  assumes "X \<in> set (tyvrs_of a)"
  shows "\<exists> U. TVarB X U = a"
  using assms
  by (nominal_induct a rule: binding.strong_induct) (auto)

lemma ty_dom_inclusion:
  assumes a: "(TVarB X T) \<in> set \<Gamma>" 
  shows "X \<in> set (ty_dom \<Gamma>)"
  using a by (induct \<Gamma>) (auto)

lemma trm_binding_existence:
  assumes "x \<in> set (vrs_of a)"
  shows "\<exists> T. VarB x T=a"
  using assms
  by(nominal_induct a rule: binding.strong_induct) auto

lemma ty_dom_existence:
  assumes a: "X \<in> set (ty_dom \<Gamma>)" 
  shows "\<exists> U. (TVarB X U) \<in> set \<Gamma>"
  using a 
  apply (induct \<Gamma>)
   apply simp
  using ty_binding_existence by auto

lemma trm_dom_existence:
  assumes a: "x \<in> set (trm_dom \<Gamma>)" 
  shows "\<exists> T. (VarB x T)\<in>set \<Gamma>"
  using assms
  apply (induct \<Gamma>)
  using trm_binding_existence by auto

lemma tyvrs_fresh:
  fixes   X::"vrs"
  assumes "atom X \<sharp> b" 
  shows   "atom X \<sharp> tyvrs_of b"
  and     "atom X \<sharp> vrs_of b"
  using assms
   apply (nominal_induct b rule:binding.strong_induct)
  by(auto simp add: fresh_Cons fresh_Nil)

lemma fresh_dom:
  fixes X::"vrs"
  assumes a: "atom X \<sharp> \<Gamma>" 
  shows "atom X \<sharp> (ty_dom \<Gamma>)"
        "atom X \<sharp> (trm_dom \<Gamma>)"
  using a
  apply(induct \<Gamma>)
  by(auto simp add: fresh_Nil fresh_Cons fresh_append tyvrs_fresh)

subsection \<open>Type ok\<close>

inductive
  valid_ty :: "env \<Rightarrow> env \<Rightarrow> env \<Rightarrow> ty \<Rightarrow> bool" ("_ ; _ ; _ \<turnstile> _ wf" [100,100,100] 100)
where
  tvar_wf[simp]: "X \<in> set (ty_dom E) \<Longrightarrow> 
                  E ; E\<^sub>1 ; E\<^sub>2 \<turnstile> (Tvar X) wf"
| top_wf[simp]: "E; E\<^sub>1; E\<^sub>2 \<turnstile> Top wf"
| capt_wf[simp]: "\<lbrakk>\<forall> X \<in> set C. X \<in> set (cv (Tvar X) (E @ E\<^sub>2) True);
                   E; E\<^sub>1; E\<^sub>2 \<turnstile> T wf\<rbrakk> \<Longrightarrow> 
                   E; E\<^sub>1; E\<^sub>2 \<turnstile> (C \<triangleright> T) wf"
| fun_wf[simp]: "\<lbrakk>E; (VarB x S # E\<^sub>1); E\<^sub>2 \<turnstile> S wf; 
                  (VarB x S # E); E\<^sub>1; E\<^sub>2 \<turnstile> T wf\<rbrakk> \<Longrightarrow> 
                  E; E\<^sub>1; E\<^sub>2 \<turnstile> (Arrow X S T) wf"
| tfun_wf[simp]: "\<lbrakk>E; (VarB x S # E\<^sub>1); E\<^sub>2 \<turnstile> S wf; 
                  (VarB x S # E); (VarB x S # E\<^sub>1); E\<^sub>2 \<turnstile> T wf\<rbrakk> \<Longrightarrow> 
                  E; E\<^sub>1; E\<^sub>2 \<turnstile> (\<forall>X<:S. T) wf"

equivariance valid_ty

nominal_inductive valid_ty done

subsection \<open>Variables in capture position\<close>

lemma or_inject: "a = b \<Longrightarrow> c = d \<Longrightarrow> (a \<or> c) = (b \<or> d)" by auto

lemma binding_some:
  fixes S Sa :: vrs and T Ta :: ty
  assumes "[[atom S]]lst. T = [[atom Sa]]lst. Ta"
  shows "[[atom S]]lst. (Some T) = [[atom Sa]]lst. (Some Ta)"
  using assms by auto

lemma binding_or:
  fixes S Sa :: vrs
  assumes "[[atom S]]lst. T = [[atom Sa]]lst. Ta"
          "[[atom S]]lst. Q = [[atom Sa]]lst. Qa"
  shows "[[atom S]]lst. (T \<or> Q) = [[atom Sa]]lst. (Ta \<or> Qa)"
  by (metis (no_types, hide_lams) Abs1_eq_iff'(3) Abs1_eq_iff_all(3) assms permute_pure) 

lemma bind_pair_add:
  fixes x xa :: vrs and S Sa T :: ty 
  assumes "atom x \<sharp> T" "atom xa \<sharp> T"
  assumes "[[atom x]]lst. S = [[atom xa]]lst. Sa"
  shows "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, T)"
  using assms 
  apply(simp add: Abs1_eq_iff(3))
  apply safe
  by(simp_all add: flip_fresh_fresh fresh_Pair)

lemma bind_pair_add_vrs:
  fixes x xa :: vrs and S Sa :: "ty" and T :: vrs
  assumes "atom T \<sharp> x" "atom T \<sharp> xa"
  assumes "[[atom x]]lst. S = [[atom xa]]lst. Sa"
  shows "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, T)"
  using assms 
  apply(simp add: Abs1_eq_iff(3))
  apply safe
  by(simp_all add: flip_fresh_fresh fresh_Pair)

lemma bind_pair_commute:
  fixes x xa :: vrs and S T Sa Ta :: ty 
  assumes "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "[[atom x]]lst. (T, S) = [[atom xa]]lst. (Ta, Sa)"
  using assms apply(simp add: Abs1_eq_iff(3))
  by fastforce

lemma bind_pair_commute_vrs1:
  fixes x xa y ya :: vrs and Sa Ta :: ty 
  assumes "[[atom x]]lst. (y, T) = [[atom xa]]lst. (ya, Ta)"
  shows "[[atom x]]lst. (T, y) = [[atom xa]]lst. (Ta, ya)"
  using assms apply(simp add: Abs1_eq_iff(3))
  by fastforce

lemma bind_pair_commute_vrs2:
  fixes x xa y ya :: vrs and Sa Ta :: ty 
  assumes "[[atom x]]lst. (T, y) = [[atom xa]]lst. (Ta, ya)"
  shows "[[atom x]]lst. (y, T) = [[atom xa]]lst. (ya, Ta)"
  using assms apply(simp add: Abs1_eq_iff(3))
  by fastforce

lemma bind_pair_proj_1:
  fixes x xa :: "'b::at" 
    and S Sa :: "'a::fs" 
    and T Ta :: "'c::fs"
  assumes "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "[[atom x]]lst. S = [[atom xa]]lst. Sa"
  using assms
  by(auto simp add: Abs1_eq_iff(3) fresh_Pair)

lemma bind_pair_proj_2:
  fixes x xa :: "'b::at" 
    and S Sa :: "'a::fs" 
    and T Ta :: "'c::fs"
  assumes "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "[[atom x]]lst. T = [[atom xa]]lst. Ta"
  using assms
  by(auto simp add: Abs1_eq_iff(3) fresh_Pair)

nominal_function in_capset :: "vrs \<Rightarrow> ty \<Rightarrow> bool" where
  "in_capset y (Tvar x) = False"
| "in_capset y Top = False"
| "atom y \<sharp> x \<Longrightarrow> in_capset y (Arrow x S T) = 
    ((in_capset y S) \<or> (in_capset y T))"
| "atom y \<sharp> X \<Longrightarrow> in_capset y (\<forall>X<:B. T) = 
    ((in_capset y B) \<or> (in_capset y T))"
| "in_capset y (C \<triangleright> T) = 
    ((y \<in> set C) \<or> (in_capset y T))"
  using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal by(simp add: eqvt_def in_capset_graph_aux_def split: option.splits)  
  subgoal premises prems for P x
  proof -
    obtain op v where x_expr: "x = (op,v)" using prod_cases by force
    show "P"
      using prems
      apply(simp add: x_expr) 
      apply(rule ty.strong_exhaust[of v P "op"]) 
          apply blast+
      using fresh_at_base(2) fresh_star_insert by fastforce+ 
  qed
  subgoal for y x S T ya xa Sa Ta
    apply(rule or_inject; elim conjE)
     apply(drule bind_pair_proj_1)
     apply(drule(2) bind_pair_add_vrs[of ya x xa S Sa])
     apply(drule bind_pair_commute_vrs2)
     apply safe
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
     apply metis
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
     apply metis
     apply(drule bind_pair_proj_2)
     apply(drule(2) bind_pair_add_vrs)
     apply(drule bind_pair_commute_vrs2)
     apply(simp_all add: Abs1_eq_iff(3)  eqvt_at_def permute_bool_def)
     apply metis
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def fresh_at_base(2))
    by (metis flip_at_base_simps(3))
  subgoal for y X B T ya Xa Ba Ta
    apply(rule or_inject; elim conjE)
    apply blast
     apply(drule(2) bind_pair_add_vrs)
     apply(drule bind_pair_commute_vrs2)
     apply safe
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
     apply metis
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
    by metis  
  done

nominal_termination (eqvt)
  by lexicographic_order

nominal_function out_capset :: "vrs \<Rightarrow> ty \<Rightarrow> bool" where
  "out_capset y (Tvar x) = (y = x)"
| "out_capset y Top = False"
| "atom y \<sharp> x \<Longrightarrow> out_capset y (Arrow x S T) = 
    ((out_capset y S) \<or> (out_capset y T))"
| "atom y \<sharp> X \<Longrightarrow> out_capset y (\<forall>X<:B. T) = 
    ((out_capset y B) \<or> (out_capset y T))"
| "out_capset y (C \<triangleright> T) = (out_capset y T)"
  using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal by(simp add: eqvt_def out_capset_graph_aux_def split: option.splits)  
  subgoal premises prems for P x
  proof -
    obtain op v where x_expr: "x = (op,v)" using prod_cases by force
    show "P"
      using prems
      apply(simp add: x_expr) 
      apply(rule ty.strong_exhaust[of v P "op"]) 
          apply blast+
      using fresh_at_base(2) fresh_star_insert by fastforce+ 
  qed
  subgoal for y x S T ya xa Sa Ta
    apply(rule or_inject; elim conjE)
     apply(drule bind_pair_proj_1)
     apply(drule(2) bind_pair_add_vrs[of ya x xa S Sa])
     apply(drule bind_pair_commute_vrs2)
     apply safe
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
     apply metis
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
     apply metis
     apply(drule bind_pair_proj_2)
     apply(drule(2) bind_pair_add_vrs)
     apply(drule bind_pair_commute_vrs2)
     apply(simp_all add: Abs1_eq_iff(3)  eqvt_at_def permute_bool_def)
     apply metis
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def fresh_at_base(2))
    by (metis flip_at_base_simps(3))
  subgoal for y X B T ya Xa Ba Ta
    apply(rule or_inject; elim conjE)
    apply blast
     apply(drule(2) bind_pair_add_vrs)
     apply(drule bind_pair_commute_vrs2)
     apply safe
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
     apply metis
     apply(simp add: Abs1_eq_iff(3) eqvt_at_def permute_bool_def)
     apply safe
    by metis  
  done

nominal_termination (eqvt)
  by lexicographic_order

lemma outcap_supp: "out_capset x T \<Longrightarrow> atom x \<in> supp T" 
  apply(nominal_induct T avoiding: x rule: ty.strong_induct)
      apply(simp_all add: ty.supp supp_at_base)
  by blast+

subsection \<open>Environment ok\<close>

definition "closed_in" :: "ty \<Rightarrow> vrs list \<Rightarrow> bool" ("_ closed'_in _" [100,100] 100) where
  "S closed_in \<Gamma> \<equiv> (supp S)\<subseteq> set (map atom \<Gamma>)"

lemma closed_in_eqvt[eqvt]:
  assumes "S closed_in \<Gamma>" 
  shows "(p\<bullet>S) closed_in (p\<bullet>\<Gamma>)" 
proof -
  from assms have "p\<bullet>(S closed_in \<Gamma>)" 
    by auto
  then show "(p\<bullet>S) closed_in (p\<bullet>\<Gamma>)" 
    by (simp add: closed_in_def)+
qed

lemma closed_in_fresh: "atom X \<sharp> ty_dom \<Gamma> \<Longrightarrow> T closed_in (ty_dom \<Gamma>) \<Longrightarrow> atom X \<sharp> T"
  by (auto simp add: closed_in_def fresh_def ty_dom_supp)

inductive
  valid_rel :: "env \<Rightarrow> bool" ("\<turnstile> _ ok" [100] 100)
where
  valid_nil[simp]:   "\<turnstile> [] ok"
| valid_consT[simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; 
                       atom X \<sharp> \<Gamma>;
                       U closed_in (X#ty_dom \<Gamma>);
                       (atom X \<in> supp U \<Longrightarrow> 
                        in_capset X U \<and> \<not> out_capset X U)\<rbrakk>  \<Longrightarrow>  
                      \<turnstile> (TVarB X U# \<Gamma>) ok"
| valid_cons [simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; 
                       atom x \<sharp> \<Gamma>;
                       T closed_in (x#ty_dom \<Gamma>);
                       (atom x \<in> supp T \<Longrightarrow> 
                       in_capset x T \<and> \<not> out_capset x T)\<rbrakk>  \<Longrightarrow>  
                      \<turnstile> (VarB x T#\<Gamma>) ok"

equivariance valid_rel
nominal_inductive valid_rel done

inductive_cases validE[elim]:
  "\<turnstile> (TVarB X U#\<Gamma>) ok" 
  "\<turnstile> (VarB x T#\<Gamma>) ok" 
  "\<turnstile> (b#\<Gamma>) ok" 

lemma ok_closed:
  assumes "\<turnstile> \<Gamma> ok"
  shows "VarB x T \<in> set \<Gamma> \<Longrightarrow> T closed_in (x # ty_dom \<Gamma>)"
  and   "TVarB X T \<in> set \<Gamma> \<Longrightarrow> T closed_in (X # ty_dom \<Gamma>)"
  using assms
   apply(induction \<Gamma> rule: valid_rel.induct)
       apply(simp_all add: closed_in_def)
  by blast+

lemma uniqueness_of_ctxt:
  fixes \<Gamma>::"env"
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "(TVarB X T)\<in>set \<Gamma>"
  and     c: "(TVarB X S)\<in>set \<Gamma>"
  shows "T=S"
using a b c
proof (induct)
  case (valid_consT \<Gamma> X' T')
  moreover
  { fix \<Gamma>'::"env"
    assume a: "atom X'\<sharp>(ty_dom \<Gamma>')" 
    have "\<not>(\<exists>T.(TVarB X' T)\<in>(set \<Gamma>'))" using a 
    proof (induct \<Gamma>')
      case (Cons Y \<Gamma>')
      thus "\<not> (\<exists>T.(TVarB X' T)\<in>set(Y#\<Gamma>'))"
        using fresh_Cons fresh_append fresh_at_base by fastforce
    qed (simp)
  }
  ultimately show "T=S" using fresh_dom by auto
qed auto

lemma uniqueness_of_ctxt':
  fixes \<Gamma>::"env"
  assumes a: "\<turnstile> \<Gamma> ok"
  and     b: "(VarB x T)\<in>set \<Gamma>"
  and     c: "(VarB x S)\<in>set \<Gamma>"
  shows "T=S"
  using a b c
proof induct
  case (valid_cons \<Gamma> x' T')
  moreover
  { fix \<Gamma>'::"env"
    assume a: "atom x'\<sharp>(trm_dom \<Gamma>')" 
    have "\<not>(\<exists>T.(VarB x' T)\<in>(set \<Gamma>'))" using a 
    proof (induct \<Gamma>')
      case (Cons y \<Gamma>')
      thus "\<not> (\<exists>T.(VarB x' T)\<in>set(y#\<Gamma>'))" 
        using fresh_Cons fresh_append fresh_at_base(2) by fastforce
    qed (simp)
  }
  ultimately show "T=S" using fresh_dom by auto
qed auto

lemma validE_append:
  assumes a: "\<turnstile> (\<Delta>@\<Gamma>) ok" 
  shows "\<turnstile> \<Gamma> ok"
  using a 
proof (induct \<Delta>)
  case (Cons a \<Gamma>')
  then show ?case 
    by (nominal_induct a rule:binding.strong_induct)
       (auto elim: validE)
qed (auto)

lemma fresh_sub_bind:
  fixes \<Gamma>::"env"
  assumes a: "\<turnstile> (\<Gamma>'@\<Gamma>) ok"
  and     b: "atom X \<in> supp (ty_dom \<Gamma>)"
  shows "atom X \<sharp> (ty_dom \<Gamma>')"
  using assms
proof (nominal_induct "\<Gamma>'@\<Gamma>" arbitrary: \<Gamma>' 
        rule: valid_rel.strong_induct)
  case valid_nil
  then show ?case by(simp add: fresh_Nil)
next
  case (valid_consT \<Gamma>'' Y U)
  then show ?case 
  proof(cases "\<Gamma>' = []")
    case False
    then obtain E where e_expr: "\<Gamma>' = [TVarB Y U] @ E" "\<Gamma>'' = E @ \<Gamma>" 
      using valid_consT(6)
      by (metis append_eq_Cons_conv self_append_conv2)
    then have "atom X \<sharp> ty_dom E"
      using valid_consT(2)[OF e_expr(2)] valid_consT(7) by fast
    then show ?thesis 
      apply(simp add: e_expr fresh_Cons)
      by (metis fresh_dom doms_append(1) e_expr(2) fresh_append fresh_def fresh_ineq_at_base valid_consT.hyps(3) valid_consT.prems)
  qed (simp add: fresh_Nil)
next
  case (valid_cons \<Gamma>'' x T)
  then show ?case 
  proof(cases "\<Gamma>' = []")
    case False
    then obtain E where e_expr: "\<Gamma>' = [VarB x T] @ E" "\<Gamma>'' = E @ \<Gamma>" 
      using valid_cons(6)
      by (metis append_eq_Cons_conv self_append_conv2)
    then have "atom X \<sharp> ty_dom E"
      using valid_cons(2)[OF e_expr(2)] valid_cons(7) by fast
    then show ?thesis 
      by(simp add: e_expr fresh_Cons)
  qed (simp add: fresh_Nil)  
qed


subsection \<open>Auxiliary functions\<close>

lemma fresh_removeAll:
  "(atom x) \<sharp> removeAll x list" 
  apply(induction list)
  by(auto simp add: fresh_Nil fresh_Cons)

lemma fresh_removeAll':
  "(atom x) \<sharp> removeAll y list \<Longrightarrow> x = y \<or> atom x \<sharp> list" 
  apply(induction list)
  by(auto simp add: fresh_Cons split: if_splits)

lemma bound_removeAll:
  assumes "[[atom x]]lst. l = [[atom xa]]lst. la"
  shows "removeAll x l = removeAll xa la"
  using assms
  apply(rule Abs_lst1_fcb2'[of _ _ _ _ _ "[]"]) 
  using fresh_removeAll apply blast
  using fresh_star_list(3) apply blast
  using removeAll_eqvt by blast+

nominal_function fv :: "trm \<Rightarrow> vrs list"
where
  "fv (Var x) = [x]"
| "fv (\<lambda>x:T. t) = removeAll x (fv t)"
| "atom X \<sharp> T  \<Longrightarrow> fv (\<lambda>X<:T. t) = removeAll X (fv t)"
| "fv (t \<cdot> s) = fv t @ fv s"
| "fv (t \<cdot>\<^sub>\<tau> T) = fv t"
  using [[simproc del: alpha_lst]]  
  apply simp_all
  subgoal by(simp add: fv_graph_aux_def eqvt_def)
  subgoal for P x
    apply(rule trm.strong_exhaust[of x P]) 
        apply( simp_all add: fresh_star_def fresh_Pair)
    by (metis Abs1_eq_iff(3) list.distinct(1) list.set_cases obtain_fresh set_ConsD trm.fresh(3))
  subgoal for x T t xa Ta ta  
  proof -
    assume 1: "[[atom x]]lst. (t, T) = [[atom xa]]lst. (ta, Ta)"
          " eqvt_at fv_sumC t" " eqvt_at fv_sumC ta"
    then have 2: "[[atom x]]lst. t = [[atom xa]]lst. ta"
      by(auto simp add: Abs1_eq_iff'(3) fresh_Pair)      
    show "removeAll x (fv_sumC t) = removeAll xa (fv_sumC ta)"
      apply(rule Abs_lst1_fcb2'[OF 2, of _ "[]"])
         apply (simp add: fresh_removeAll)
        apply (simp add: fresh_star_list(3))
      using 1 Abs_lst1_fcb2' unfolding eqvt_at_def
      by auto
  qed
  subgoal for X T t Xa Ta ta 
  proof(safe)
    assume 1: "[[atom X]]lst. t = [[atom Xa]]lst. ta"
          " eqvt_at fv_sumC t" " eqvt_at fv_sumC ta"
    show "removeAll X (fv_sumC t) = removeAll Xa (fv_sumC ta)"
      apply(rule Abs_lst1_fcb2'[OF 1(1), of _ "[]"])
         apply (simp add: fresh_removeAll)
        apply (simp add: fresh_star_list(3))
      using 1 Abs_lst1_fcb2' unfolding eqvt_at_def
      by auto
  qed
  done

nominal_termination (eqvt)
  by lexicographic_order

subsection \<open>Subtype extraction\<close>

nominal_function extract_subtype_b :: "vrs \<Rightarrow> binding \<Rightarrow> ty option" where
  "extract_subtype_b x (VarB y T) = None"
| "extract_subtype_b x (TVarB y T) = (if x = y then Some T else None)"
  apply simp_all
  subgoal by(simp add: eqvt_def extract_subtype_b_graph_aux_def)
  subgoal for P x
    apply(cases x,rule binding.strong_exhaust)
    by blast+
  done

nominal_termination (eqvt)
  by lexicographic_order


nominal_function extract_type_b :: "vrs \<Rightarrow> binding \<Rightarrow> ty option" where
  "extract_type_b x (VarB y T) = (if x = y then Some T else None)"
| "extract_type_b x (TVarB y T) = None"
  apply simp_all
  subgoal by(simp add: eqvt_def extract_type_b_graph_aux_def)
  subgoal for P x
    apply(cases x,rule binding.strong_exhaust)
    by blast+
  done
                    
nominal_termination (eqvt)
  by lexicographic_order

primrec extract_subtype :: "vrs \<Rightarrow> env \<Rightarrow> ty option \<times> env" where
  "extract_subtype x [] = (None, []) "
| "extract_subtype x (b # bs) = 
    (case (extract_subtype_b x b) of
      None \<Rightarrow> extract_subtype x bs
    | Some T \<Rightarrow> (Some T, bs))
    "

lemma extract_subtype_eqvt [eqvt]:
  shows "p \<bullet> (extract_subtype x l) = extract_subtype (p \<bullet> x) (p \<bullet> l)"
proof(induct l)
  case (Cons a l)
  show ?case
    apply(rule binding.strong_exhaust[of a])
    by(auto simp add: Cons)
qed auto

primrec extract_types :: "vrs \<Rightarrow> env \<Rightarrow> ty option" where
  "extract_types x [] = (None::ty option)"
| "extract_types x (b # bs) = 
    (case (extract_type_b x b) of
      None \<Rightarrow> None
    | Some T \<Rightarrow> Some T)
    "

lemma extract_type_eqvt [eqvt]:
  shows "p \<bullet> (extract_types x l) = extract_types (p \<bullet> x) (p \<bullet> l)"
proof(induct l)
  case (Cons a l)
  show ?case
    apply(rule binding.strong_exhaust[of a])
    by auto
qed auto

lemma extract_subtype_b_iff:
  "extract_subtype_b x b = Some T \<longleftrightarrow> (b = TVarB x T)"
   apply(rule binding.strong_exhaust[of b])
  by(simp split: if_splits)+

lemma extract_subtype_if:
  "extract_subtype x E = (Some T,E') \<Longrightarrow>
       (TVarB x T \<in> set E)"
   apply(induction E)
  by(simp_all add: extract_subtype_b_iff split: option.splits)

lemma extract_remainder:
  assumes "extract_subtype x E = (Some T, E')"
  shows "\<exists> E''. E = E'' @ TVarB x T # E'"
  using assms
  apply(induction E)
  subgoal by simp
  subgoal for a l
    apply simp
    apply(cases "a" rule: binding.strong_exhaust)
    by(auto simp add: split: if_splits)
  done

lemma extract_dec_length:
  shows "extract_subtype x E = (Some T, E') \<Longrightarrow> 
         length E' < length E"
  apply(drule extract_remainder)
  apply safe
  by simp

lemma extract_subtype_if_some:
  "(TVarB x T \<in> set E) \<Longrightarrow>
     (\<exists> B E'. extract_subtype x E = (B, E'))"
  apply(induction E)
  by(auto split: option.splits)

lemma extract_subtype_iff:
  assumes "\<turnstile> E ok"
  shows "(\<exists> E'. extract_subtype x E = (Some T,E')) \<longleftrightarrow> (TVarB x T \<in> set E)"
proof safe
  assume 1: "TVarB x T \<in> set E"
  show "\<exists> E'. extract_subtype x E = (Some T,E')"
    using assms 1
  proof(nominal_induct rule: valid_rel.strong_induct)
    case (valid_consT \<Gamma> X U)
    then have 2: "\<turnstile> (TVarB X U # \<Gamma>) ok" by simp
    from valid_consT consider 
      (a) "TVarB x T = TVarB X U"
    | (b) "TVarB x T \<in> set \<Gamma>" "TVarB x T \<noteq> TVarB X U" by auto
    then show ?case 
    proof(cases)
      case a then show ?thesis by force
    next
      case b
      then have 3: "x \<noteq> X"
        using uniqueness_of_ctxt[OF 2, of x T U] by auto
      from b have "x \<in> set (ty_dom \<Gamma>)"
        using ty_dom_inclusion by auto
      show ?thesis 
        by(simp add: 3 valid_consT.hyps(2) b)
    qed
  qed auto
qed (simp add: extract_subtype_if)

(*
lemma extraction_monotonic:
  assumes "set E \<subseteq> set E'"
          "extract_subtype x E = (Some T, E'')"         
  shows "\<exists> Q E'''. extract_subtype x E' = (Some Q, E''')"
proof -
  have "TVarB x T \<in> set E"
    using assms extract_subtype_if by blast
  then have "TVarB x T \<in> set E'"
    using assms(1) by blast
  then show ?thesis
    using extract_subtype_if_some by blast
qed

lemma uniqueness_of_extraction:
  assumes "extract_subtype x E = Some T"
          "extract_subtype x E' = Some Q"
          "set E \<subseteq> set E'"
          "\<turnstile> E' ok"
  shows "T = Q"
  by (meson assms extract_subtype_if in_mono uniqueness_of_ctxt)
*)
lemma extract_fresh_none:
  assumes "atom x \<sharp> ty_dom \<Gamma>"
  shows "extract_subtype x \<Gamma> = (None,[])"
  using assms
proof(induction \<Gamma>)
  case (Cons a \<Gamma>)
  then show ?case 
    apply(simp add: fresh_append split: option.splits) 
    apply(cases a rule: binding.strong_exhaust)
    by (simp_all add: fresh_Cons fresh_at_base(2))
qed simp

lemma extract_append:
  assumes "extract_subtype x E = (Some T,E'')"
          "\<turnstile> (E' @ E) ok"
  shows "\<exists> E'''. extract_subtype x (E' @ E) = (Some T, E''')"
  using assms
  apply(induction E')
  apply(simp_all split: option.splits, safe)
  using extract_fresh_none extract_subtype_b_iff fresh_dom by auto

lemma extract_skip_fresh:
  assumes "atom x \<sharp> (ty_dom E')"
  shows "extract_subtype x (E' @ E) = 
         extract_subtype x E"
  using assms
  apply(induction E')
   apply(simp_all add: fresh_Cons fresh_append split: option.splits prod.splits)
  apply safe
  by (simp add: extract_subtype_b_iff fresh_Cons fresh_at_base(2))

lemma fresh_extract:
  assumes "atom x \<sharp> E"
          "extract_subtype x1 E = (Some T,E')"
  shows "atom x \<sharp> T"
  using assms
proof(induction E)
  case (Cons a E)
  then show ?case 
    apply(simp add: fresh_Cons split: option.splits)
    apply(cases "a" rule: binding.strong_exhaust)
    by(simp_all split: if_splits)
qed simp

lemma extract_none_imp_nil:
  assumes "extract_subtype x1 E = (None, E')" 
  shows "E' = []"
  using assms
  apply(induction E)
  by(simp_all split: option.splits)

lemma extract_none_imp_fresh:
  assumes "extract_subtype x E = (None, [])" 
  shows "atom x \<sharp> ty_dom E"
  using assms
  apply(induction E)
   apply(simp_all add: fresh_Nil fresh_Cons split: option.splits)
  subgoal for a E
    apply(cases a rule: binding.strong_exhaust)
    by(simp_all add: fresh_Cons split: if_splits)
  done

lemma extract_some:
  assumes "extract_subtype X E = (Some T, E')"
  shows "(\<exists> E''. E = E'' @ [TVarB X T] @ E' \<and> atom X \<sharp> (ty_dom E''))"
  using assms
proof(induction E)
  case (Cons a E)
  then show ?case 
    apply(simp split: option.splits)
    apply (metis append_Cons extract_fresh_none extract_none_imp_fresh extract_subtype.simps(2) option.case_eq_if)
    apply safe    
    apply(cases a rule: binding.strong_exhaust)
    by(simp_all add: fresh_Nil split: if_splits)
qed simp

lemma extract_monotonic:
  assumes "set E \<subseteq> set E'"
          "extract_subtype X E = (Some T, E'')"
  shows "\<exists> T' E'''. extract_subtype X E' = (Some T', E''')"
  using assms
  apply(induction E arbitrary: )
   apply(simp_all split: option.splits)
  apply safe
  subgoal for a E x2
    apply(cases a rule: binding.strong_exhaust)
     apply(simp_all split: if_splits)
  proof -
    fix x21 :: vrs and x22 :: ty
    assume "X = x21"
    assume a1: "a = TVarB x21 T"
    assume "x22 = T"
assume a2: "TVarB x21 T \<in> set E'"
obtain zz :: "ty option \<times> binding list \<Rightarrow> ty option" and bbs :: "ty option \<times> binding list \<Rightarrow> binding list" where
  f3: "\<forall>p. p = (zz p, bbs p)"
by (meson old.prod.exhaust)
  have "\<forall>aa. aa \<sharp> tyvrs_of a \<or> \<not> aa \<sharp> ty_dom E'"
    using a2 a1 by (metis (no_types) doms_append(1) fresh_append in_set_conv_decomp ty_dom.simps(2))
  then show "\<exists>t bs. extract_subtype x21 E' = (Some t, bs)"
    using f3 a1 by (metis extract_none_imp_fresh extract_none_imp_nil fresh_Cons fresh_at_base(2) option.exhaust_sel tyvrs_of.simps(2))
qed
  done

lemma append_extract:
  assumes "extract_subtype x E = (None, \<Gamma>)"
          "extract_subtype x (E' @ E) = (Some T, \<Gamma>')"
  obtains E\<^sub>1 E\<^sub>2 where 
          "extract_subtype x E' = (Some T, E\<^sub>1)"
          "E' = E\<^sub>2 @ E\<^sub>1" "\<Gamma>' = E\<^sub>1 @ E"
  using assms
proof(induction E')
  case (Cons a E')
  then show ?case 
    apply(simp_all split: option.splits)
    apply(simp add: Cons.prems(1))
    apply(drule extract_none_imp_nil)
    by (simp add: Cons.prems(1))
qed simp

lemma extract_wf_unique:
  assumes "\<turnstile> E ok" "\<turnstile> E' ok" "set E \<subseteq> set E'"
  assumes "extract_subtype x E = (Some T, E'')"
          "extract_subtype x E' = (Some T', E''')"
  shows "T = T'" 
  by (meson assms(2) assms(3) assms(4) assms(5) extract_subtype_if in_mono uniqueness_of_ctxt)

subsection \<open>Occurs covariantly\<close>

nominal_function occurs_cov :: "ty \<Rightarrow> ty \<Rightarrow> bool \<Rightarrow> bool" where
  "occurs_cov Q (Tvar x) b = (b \<and> Q = Tvar x)"
| "occurs_cov Q Top b = (b \<and> Q = Top)"
| "atom x \<sharp> Q \<Longrightarrow> occurs_cov Q (Arrow x S T) b = 
   (occurs_cov Q S (\<not> b) \<or> occurs_cov Q T b)"
| "atom X \<sharp> Q \<Longrightarrow> occurs_cov Q (\<forall>X<:B. T) b = 
    (occurs_cov Q B (\<not> b) \<or> occurs_cov Q T b)"
| "occurs_cov Q (C \<triangleright> T) b = occurs_cov Q T b"
  using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal by(simp add: eqvt_def occurs_cov_graph_aux_def split: option.splits)
  subgoal premises prems for P x
  proof -
    obtain Q T b where x_expr: "x = (Q,T,b)" using prod_cases3 by blast 
    show "P"
      using prems
      apply(simp add: x_expr)   
      apply(rule ty.strong_exhaust) 
      using fresh_star_insert fresh_PairD by fastforce+
  qed
  subgoal for x Q S T b xa Qa Sa Ta ba
    apply(rule or_inject) 
     apply(rule Abs_lst1_fcb2'[of x "(Qa,S)" xa "(Qa,Sa)" 
            "(\<lambda> a. \<lambda> (b,c). \<lambda> d. occurs_cov_sumC (b, c, \<not> ba))" "[]", simplified]) 
         apply(rule bind_pair_commute)
         apply(rule bind_pair_add)
           apply blast+
         apply(rule bind_pair_proj_1[of _ _ T _ _ Ta])
         apply blast+
    using pure_fresh apply blast
    using fresh_star_list(3) apply blast
    unfolding eqvt_at_def apply force
    unfolding eqvt_at_def apply force
    apply(rule Abs_lst1_fcb2'[of x "(Qa,T)" xa "(Qa,Ta)" 
            "(\<lambda> a. \<lambda> (b,c). \<lambda> d. occurs_cov_sumC (b, c, ba))" "[]", simplified]) 
         apply(rule bind_pair_commute)
         apply(rule bind_pair_add)
           apply blast+
         apply(rule bind_pair_proj_2[of _ _ T _ _ Ta])
         apply blast+
    using pure_fresh apply blast
    using fresh_star_list(3) apply blast
    unfolding eqvt_at_def apply force
    unfolding eqvt_at_def by force
  subgoal for X Q B T b Xa Qa Ba Ta ba
    apply(rule or_inject) 
     apply fast
     apply(rule Abs_lst1_fcb2'[of X "(Qa,T)" Xa "(Qa,Ta)" 
            "(\<lambda> a. \<lambda> (b,c). \<lambda> d. occurs_cov_sumC (b, c, ba))" "[]", simplified]) 
         apply(rule bind_pair_commute)
         apply(rule bind_pair_add)
           apply blast+
    using pure_fresh apply blast
    using fresh_star_list(3) apply blast
    unfolding eqvt_at_def apply force
    unfolding eqvt_at_def by force
  done

nominal_termination (eqvt)
  by lexicographic_order

subsection \<open>Cv function\<close>

nominal_function cv :: "ty \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> vrs list"
where
  "cv (Tvar x) E b = 
    (if b 
     then (case (extract_subtype x E) of
                 (Some T,E') \<Rightarrow> (cv T E' True)
               | (None,E') \<Rightarrow> []) 
     else [])"
| "cv Top E b = []"
| "atom x \<sharp> E \<Longrightarrow> cv (Arrow x S T) E b = 
    removeAll x (cv S E (\<not> b) @ cv T E b)" 
| "atom X \<sharp> E \<Longrightarrow> cv (\<forall>X<:B. T) E b = 
    cv B E (\<not> b) @ (removeAll X (cv T E b))"
| "cv (C \<triangleright> T) E b = 
    (if b then C @ cv T E True else cv T E False)"
  using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal 
    by(simp add: eqvt_def cv_graph_aux_def split: option.splits prod.splits)
  subgoal premises prems for P x
  proof -
    obtain op E b where x_expr: "x = (op,E,b)" using prod_cases3 by blast  
    show "P"
      using prems
      apply(simp add: x_expr)   
      apply(rule ty.strong_exhaust[of op P "E"]) 
          apply(simp_all add: fresh_Pair)
      using fresh_star_insert fresh_PairD by blast+
  qed
  subgoal for x E S T b xa Ea Sa Ta ba
    apply(rule arg_cong2[of _ _ _ _ append]) 
    subgoal
      apply(rule bound_removeAll)
      apply(elim conjE)
      apply(drule bind_pair_proj_1)
    apply(erule Abs_lst1_fcb2')
       apply (simp add: Abs_fresh_iff(3))
      apply(simp add: pure_fresh fresh_star_def fresh_Pair)
     apply(simp_all add: eqvt_at_def permute_bool_def)
      by(simp_all add: fresh_star_Pair perm_supp_eq)
    subgoal
      apply(rule bound_removeAll)
      apply(elim conjE)
      apply(drule bind_pair_proj_2)
    apply(erule Abs_lst1_fcb2')
       apply (simp add: Abs_fresh_iff(3))
      apply(simp add: pure_fresh fresh_star_def fresh_Pair)
     apply(simp_all add: eqvt_at_def permute_bool_def)
      by(simp_all add: fresh_star_Pair perm_supp_eq)
    done  
  subgoal for X E B T b Xa Ea Ba Ta ba
    apply(rule bound_removeAll)
    apply(elim conjE)
    apply(erule Abs_lst1_fcb2')
       apply (simp add: Abs_fresh_iff(3))
      apply(simp add: pure_fresh fresh_star_def fresh_Pair)
     apply(simp_all add: eqvt_at_def permute_bool_def)
    by (simp_all add: fresh_star_Pair perm_supp_eq)
  done

nominal_termination (eqvt)
  apply(relation "
         (\<lambda> (a,b,c). length b) <*mlex*> 
         (\<lambda> (a,b,c). size a)  <*mlex*> {}", goal_cases) 
  apply(simp_all add: wf_mlex mlex_leq extract_subtype_if length_removeAll_less mlex_less)
  apply(simp add: mlex_iff)
  by (metis extract_dec_length)

subsubsection \<open>Lemmas related to cv\<close>

lemma cv_ignore_extra:
  assumes "\<turnstile> (E' @ E) ok" 
          "(supp U)\<subseteq> set (map atom (ty_dom E)) \<union>
                     {x. x \<sharp> (E,E')}" 
  shows "cv U (E' @ E) b = cv U E b"
  using assms
proof(induction "(length (E' @ E), size U)"
        arbitrary: U E E' b rule: less_induct)
  case less
  show ?case 
    apply(cases rule: ty.strong_exhaust[of U _ "E'@E"])
    subgoal for x1 
      apply(simp only: cv.simps split: if_splits option.splits prod.splits)
      apply safe
      using extract_append less.prems(1) apply fastforce
      subgoal for x1a x2 x2a x1aa x2b
      proof -
        assume "extract_subtype x1 E = (None, x2b)" 
        then have 1: "atom x1 \<sharp> ty_dom E"
          using extract_none_imp_fresh extract_none_imp_nil by blast
        assume "U = Tvar x1" 
        then have "{atom x1} \<subseteq> {x. x \<sharp> (E,E')}"
          using less
          by (smt "1" Un_iff fresh_def less.prems(2) singletonD subset_iff supp_at_base ty.supp(1) ty_dom_supp(1))
        then have "atom x1 \<sharp> ty_dom (E @ E')"
          by(simp add: doms_append fresh_append fresh_Pair fresh_dom)
        then have "extract_subtype x1 (E' @ E) = (None, [])"
          by (simp add: doms_append(1) extract_fresh_none fresh_append)
        assume "extract_subtype x1 (E' @ E) = (Some x2a, x2)"
        then show ?thesis
          by (simp add: \<open>extract_subtype x1 (E' @ E) = (None, [])\<close>)
      qed     
      subgoal for x1a x2 x2a x1aa x2b x2c
      proof -
        assume 1: "extract_subtype x1 E = (Some x2c, x2b)"
        then have "TVarB x1 x2c \<in> set E" 
          using extract_subtype_if by blast
        then have "atom x1 \<in> supp (ty_dom E)"       
          using 1 extract_fresh_none fresh_def fresh_dom by fastforce
        then have 2: "atom x1 \<sharp> ty_dom E'"
          using fresh_sub_bind less.prems(1) by blast
        assume 3: "extract_subtype x1 (E' @ E) = (Some x2a, x2)" 
        then have "x2a = x2c" "x2 = x2b"
          using extract_skip_fresh[OF 2, of E] 1 3 by force+
        then show "cv x2a x2 True = cv x2c x2b True" by auto
      qed
      done
    subgoal by simp
    subgoal for x31 x32 x33
      apply(simp add: fresh_star_def fresh_append fresh_Pair)     
      apply safe
       apply(rewrite removeAll_append[symmetric])+
       apply(rule arg_cong2[of x31 x31 _ _ removeAll, simplified])
      apply(rule arg_cong2[of _ _ _ _ append])
      thm less(1)[of ]
        apply(rule less(1))
           apply(simp_all add: less)
      using less(3) apply(simp add: ty.supp)
        apply safe
        apply auto[1]
       apply(rule less(1))
          apply(simp_all add: less)
      using less(3) apply(simp add: ty.supp)
       apply safe
      by auto[1]  
    subgoal for x41 x42 x43
      apply(simp add: fresh_star_def fresh_append fresh_Pair)     
      apply safe
       apply(rule arg_cong2[of _ _ _ _ append])
        apply(rule less(1))
           apply(simp_all add: less)
      using less(3) apply(simp add: ty.supp)
       apply(rule arg_cong2[of _ _ _ _ removeAll, simplified])
      apply simp
      apply(rule less(1))
          apply(simp_all add: less)
        using less(3) apply(simp add: ty.supp)
        using less(3) apply(simp add: ty.supp)
         apply safe
        by auto[1]
    subgoal for x51 x52
      apply simp
      apply safe
       apply(subst less(1))
      apply(simp_all add: less)
      using closed_in_def less.prems(2) ty.supp(5) apply auto[1]
      apply(subst less(1))
      apply(simp_all add: less)
      using closed_in_def less.prems(2) ty.supp(5) by auto[1]
    done
qed

lemma remove_not_cap:
  assumes "\<not> (out_capset y T)"
  shows "cv T (TVarB y T' # E) b = cv T E b"
  using assms
proof(induction "size T"
        arbitrary: y T E T' b rule: less_induct)
  case less
  show ?case 
    apply(cases rule: ty.strong_exhaust[of T _ "(y,E,T')"])
    subgoal for x1
      apply(simp only: cv.simps split: if_splits option.splits prod.splits)
      apply safe
      using less.prems by auto
    subgoal by simp
    subgoal for x31 x32 x33
    proof -
      assume 1: "T = Arrow x31 x32 x33" 
      assume 2: "{atom x31} \<sharp>* (y, E, T')" 
      from 2 have 3: "atom x31 \<sharp> (TVarB y T' # E)" 
        by(simp add: fresh_star_def fresh_Cons fresh_Pair)
      from 1 2 3 show ?thesis
        apply(simp add: fresh_star_def fresh_Pair)
        apply safe
        apply(rule arg_cong2[of _ _ _ _ append])
        apply(rule arg_cong2[of _ _ _ _ removeAll], simp)
         apply(rule less(1))
        apply simp
        using less apply simp
        using less.prems apply auto[1]
        apply(rule arg_cong2[of _ _ _ _ removeAll], simp)
        apply(rule less(1))
        apply simp
        using less by simp
    qed
    subgoal for x41 x42 x43
    proof -
      assume 1: "T = (\<forall>x41<:x43. x42)" 
      assume 2: "{atom x41} \<sharp>* (y, E, T')" 
      from 2 have 3: "atom x41 \<sharp> (TVarB y T' # E)" 
        by(simp add: fresh_star_def fresh_Cons fresh_Pair)
      from 1 2 3 show ?thesis
        apply(simp add: fresh_star_def fresh_Pair)
        apply safe
        apply(rule arg_cong2[of _ _ _ _ append])
         apply(rule less(1))
        apply simp
        using less apply simp
        using less.prems apply auto[1]
        apply(rule arg_cong2[of _ _ _ _ removeAll], simp)
        apply(rule less(1))
        apply simp
        using less by simp
    qed
    subgoal for x51 x52
      apply simp
      apply safe  
      apply(rule less(1))
        apply(simp_all add: less)
      using less.prems apply auto[1]
      apply(rule less(1))
        apply(simp_all add: less)
      using less.prems by auto[1]
    done
qed

lemma ncv_fresh_ty_env:
  assumes "\<turnstile> E ok" "atom x \<sharp> T" "atom x \<sharp> E"
  shows "x \<notin> set (cv T E b)"
  using assms
proof(induction "(length E, size T)"
        arbitrary: T E b rule: less_induct)
  case less
  then show ?case 
    apply(cases rule: ty.strong_exhaust[of T _ "(E,S)"])
    subgoal for x1
      apply(simp only: cv.simps split: if_split option.splits prod.splits)
      apply safe
         apply simp_all
      by (metis extract_dec_length extract_some fresh_append fresh_extract validE_append)
    subgoal by simp
    subgoal for x31 x32 x33
      unfolding fresh_star_def
      apply(simp add: fresh_Pair)
      apply safe
      by force+
    subgoal for x41 x42 x43
      unfolding fresh_star_def
      apply(simp add: fresh_Pair)
      apply safe
      by force+
    subgoal for x51 x52
      by(simp add: fresh_vrs_list)
    done     
qed

subsubsection \<open>Characterization of cv\<close>

lemma cv_implies_1:
  shows "set C \<subseteq> set (cv (C \<triangleright> T) E True)" by simp

lemma cv_implies_2:
  assumes "\<turnstile> E ok" "TVarB x T \<in> set E"
  shows "cv (Tvar x) E True = cv T E True"
  using assms
  apply(simp only: cv.simps split: if_splits option.splits prod.splits)
  apply safe
  using extract_subtype_iff[OF assms(1), of x T] apply simp
  using extract_subtype_iff[OF assms(1), of x T] apply simp
  subgoal for x2 x2a
  proof -
    assume "\<turnstile> E ok" 
    assume "extract_subtype x E = (Some T, x2)"
    then obtain E'' where 1: "E = E'' @ [TVarB x T] @ x2" 
                             "atom x \<sharp> (ty_dom E'')"     
      using extract_some by blast
    then have "cv T E True = cv T ([TVarB x T] @ x2) True"
      by (smt append_Cons append_self_conv2 assms(1) closed_in_def cv_ignore_extra sup.coboundedI1 ty_dom.simps(2) tyvrs_of.simps(2) validE(1) validE_append)
    also have "... = cv T x2 True"      
    proof(cases "\<not> out_capset x T")
      case True
      then show ?thesis by (simp add: remove_not_cap)
    next
      case False
      have 2: "\<turnstile> (TVarB x T # x2) ok" 
        using "1"(1) assms(1) validE_append by auto
      then have "\<not> out_capset x T"
        using outcap_supp by blast
      then show ?thesis
        using False by auto
    qed
    finally show ?thesis by auto
  qed
  done

lemma cv_implies_3:
  assumes "\<turnstile> E ok" "occurs_cov S T b"
  shows "set (cv S E True) \<subseteq> set (cv T E b)"
  using assms
proof(nominal_induct T avoiding: S E arbitrary: b rule: ty.strong_induct)
  case (Tvar x)
  then show ?case by(simp only: occurs_cov.simps)
next
  case Top
  then show ?case by(simp only: occurs_cov.simps)
next
  case (Arrow x1 x2 x3)
  then show ?case 
    apply(simp add: fresh_Nil)
    apply(cases "b"; elim disjE)
    by(auto simp add: le_supI1 le_supI2 ncv_fresh_ty_env subset_Diff_insert)
next
  case (Forall x1 x2 x3)
  then show ?case 
    apply(simp add: fresh_Nil)
    apply(cases "b"; elim disjE)
    by(auto simp add: le_supI1 le_supI2 ncv_fresh_ty_env subset_Diff_insert)
next
  case (CapSet x1a x2)
  then show ?case 
    apply(simp add: fresh_Nil)
    apply(cases "b") 
    by auto
qed

subsubsection \<open>Extra cv functions\<close>

definition cv_vrs :: "vrs \<Rightarrow> env \<Rightarrow> vrs list" where
  "cv_vrs x E = (case (extract_types x E) of
                 Some T \<Rightarrow> (cv T (removeAll (VarB x T) E) True)
                | None \<Rightarrow> [])"

lemma cv_vrs_eqvt [eqvt]:
  shows "p \<bullet> (cv_vrs x E) = cv_vrs (p \<bullet> x) (p \<bullet> E)"
  unfolding cv_vrs_def
  apply(simp split: option.splits)
  by(safe;
        subst (asm) extract_type_eqvt[symmetric];
        simp)

definition cv_trm :: "trm \<Rightarrow> env \<Rightarrow> vrs list" where
 "cv_trm t E = concat (map (\<lambda> fv. (cv_vrs fv E)) (fv t))"

lemma concat_eqvt[eqvt]: "p \<bullet> concat l = concat (p \<bullet> l)"
  apply(induction l)
  by (auto simp add: append_eqvt)

lemma cv_trm_eqvt [eqvt]:
  shows "p \<bullet> (cv_trm x E) = cv_trm (p \<bullet> x) (p \<bullet> E)"
  unfolding cv_trm_def by simp

nominal_function is_val :: "trm \<Rightarrow> bool"
where
  "is_val (\<lambda>x: T. t) = True"
| "is_val (\<lambda>X<:T. t) = True"
| "is_val (Var x) = False"
| "is_val (t \<cdot> s) = False"
| "is_val (t \<cdot>\<^sub>\<tau> S) = False"
  using [[simproc del: alpha_lst]]  
  apply simp_all
  subgoal by(simp add: is_val_graph_aux_def eqvt_def)
  subgoal for P x
    apply(rule trm.strong_exhaust[of x P]) 
    by simp_all
  done

nominal_termination (eqvt)
  by lexicographic_order

subsubsection \<open>Monotonicity of cv\<close>

lemma cv_append_mono:
  assumes "\<turnstile> (E' @ E) ok"
  shows "set (cv T E b) \<subseteq> set (cv T (E' @ E) b)"
  using assms
  apply(nominal_induct T avoiding: E E' arbitrary: b rule: ty.strong_induct)
  subgoal for x1 E E'
      apply(simp only: cv.simps split: if_splits prod.splits option.splits)
      apply safe
      apply simp
    subgoal for l x2 x2a z x2b x    
      apply(frule extract_none_imp_nil)
      apply simp
      apply(drule extract_none_imp_fresh)
      apply(drule extract_some)
      apply simp
      using doms_append(1) fresh_vrs_list by fastforce
    subgoal for x1a x2 x2a x1aa x2b x2c x
      apply(drule extract_some)
      apply(simp,safe)
      apply(subst (asm) (2) append.assoc[symmetric])
      subgoal for E''
        apply(subst (asm) extract_skip_fresh[of x1 "E' @ E''"])
         apply(simp add: doms_append fresh_append)
        apply (meson fresh_def fresh_sub_bind fresh_vrs_list in_set_conv_decomp ty_dom_inclusion)
        by simp
      done
    done
  subgoal by simp
  subgoal for x1a x2 x3 E E' b
    apply(simp add: fresh_star_def fresh_Pair fresh_append)
    apply safe
    by blast+
  subgoal for x1a x2 x3 E E' b
    apply(simp add: fresh_star_def fresh_Pair fresh_append)
    apply safe
    by blast+
  subgoal for x1a x2 E E' b
    apply(simp add: fresh_star_def fresh_Pair fresh_append)
    apply safe
    by blast+
  done
(*
lemma cv_mono:
  assumes "\<turnstile> E ok" "\<turnstile> E' ok"
  assumes "set E \<subseteq> set E'"
  shows "set (cv T E b) \<subseteq> set (cv T E' b)"
  using assms
proof(induction "length E"
        arbitrary: E E' T b rule: less_induct)
  case less
  show ?case
  apply(cases T rule: ty.strong_exhaust)
  subgoal for x1
    apply(simp only: cv.simps split: if_splits prod.splits option.splits)
    apply safe
      apply simp_all
    apply (metis Pair_inject extract_monotonic less.prems option.distinct(1))
    subgoal for x2 x2a x2b x2c x
    proof -
      assume 1: "x \<in> set (cv x2a x2 True)" 
      assume "extract_subtype x1 E = (Some x2a, x2)" 
             "extract_subtype x1 E' = (Some x2c, x2b)" 
      then have "x2a = x2c" 
        using extract_wf_unique less.prems(1) less.prems(2) less.prems(3) by blast
      then show ?thesis
        using 1 less 
    qed
*)
lemma cv_env_weakening:
  assumes "\<turnstile> (\<Delta> @ B @ \<Gamma>) ok" "\<turnstile> (\<Delta> @ \<Gamma>) ok"
  shows "set (cv T (\<Delta> @ B @ \<Gamma>) b) \<supseteq> 
         set (cv T (\<Delta> @ \<Gamma>) b)"
  using assms
proof(induction "(length \<Delta>, size T)"
        arbitrary: \<Delta> T b rule: less_induct)
  case less
  show ?case
    apply(cases rule: ty.strong_exhaust[of T _ "(\<Delta>, B, \<Gamma>)"])
    subgoal for x1
      apply(simp only: cv.simps split: if_splits prod.splits option.splits)
      apply safe
        apply simp_all      
      apply (metis doms_append(1) empty_iff extract_fresh_none extract_none_imp_fresh extract_none_imp_nil extract_subtype.simps(1) extract_subtype_if fresh_append list.set(1))
      subgoal for x2 x2a x2b x2c x
      proof -
        assume 0: "x \<in> set (cv x2a x2 True)" 
        assume 1: "extract_subtype x1 (\<Delta> @ \<Gamma>) = (Some x2a, x2)"
                  "extract_subtype x1 (\<Delta> @ B @ \<Gamma>) = (Some x2c, x2b)"
        then have eq1: "x2a = x2c" 
          by (metis Un_iff extract_subtype_if less.prems(1) set_append uniqueness_of_ctxt)
        from 1(1) 
        consider (a) "TVarB x1 x2a \<in> set \<Delta>" | (b) "TVarB x1 x2a \<in> set \<Gamma>" 
          using extract_subtype_if by fastforce
        then show ?thesis
        proof(cases)
          case a
          then obtain \<Delta>' \<Delta>'' where 
            delta_eq: "\<Delta> = \<Delta>' @ [TVarB x1 x2a] @ \<Delta>''" 
            using split_list by fastforce
          also have "atom x1 \<sharp> (ty_dom \<Delta>')" "atom x1 \<sharp> (ty_dom \<Delta>'')" 
            using calculation fresh_sub_bind less.prems(2) ty_dom_supp(1) apply fastforce
            by (metis fresh_dom append_Cons append_assoc calculation doms_append(1) fresh_append less.prems(2) validE(1) validE_append)
          moreover have x_expr: "x2 = \<Delta>'' @ \<Gamma>" "x2b = \<Delta>'' @ B @ \<Gamma>"
            using 1(1)
            apply(simp add: delta_eq)
            apply(subst (asm) extract_skip_fresh, simp add: calculation) 
            apply simp
            using 1(2)
            apply(simp add: delta_eq)
            apply(subst (asm) extract_skip_fresh, simp add: calculation) 
            by simp 
          have "set (cv x2a x2 True) \<subseteq> set (cv x2c x2b True)"  
            apply(simp add: x_expr eq1)
            apply(rule less(1)[of \<Delta>''])
              apply(simp_all add: delta_eq less)
            using delta_eq less.prems validE_append by auto
          then show ?thesis
            using 0 by fast
        next                
          case b
          then obtain \<Gamma>' \<Gamma>'' where 
            delta_eq: "\<Gamma> = \<Gamma>' @ [TVarB x1 x2a] @ \<Gamma>''" 
            using split_list by fastforce
          also have "atom x1 \<sharp> (ty_dom \<Gamma>')" 
                    "atom x1 \<sharp> (ty_dom \<Gamma>'')" 
                    "atom x1 \<sharp> (ty_dom B)"
                    "atom x1 \<sharp> (ty_dom \<Delta>)"
            apply (metis append_Cons delta_eq fresh_def fresh_sub_bind fresh_vrs_list less.prems(2) list.set_intros(1) ty_dom.simps(2) tyvrs_of.simps(2) validE_append)
             apply (metis fresh_dom append_Cons calculation doms_append(1) fresh_append less.prems(2) validE(1) validE_append)
            using b fresh_def fresh_sub_bind fresh_vrs_list less.prems(1) ty_dom_inclusion validE_append apply blast
            using b fresh_def fresh_sub_bind fresh_vrs_list less.prems(2) ty_dom_inclusion by blast
          moreover have x_expr: "x2 = \<Gamma>''" "x2b = \<Gamma>''"
            using 1(1)
            apply(simp add: delta_eq)
            apply(subst (asm) extract_skip_fresh, simp add: calculation) 
            apply(subst (asm) extract_skip_fresh, simp add: calculation) 
             apply simp
            using 1(2)
             apply(simp add: delta_eq)
            apply(subst (asm) extract_skip_fresh, simp add: calculation)+ 
            by simp
           have "set (cv x2a x2 True) \<subseteq> set (cv x2c x2b True)"  
             by(simp add: x_expr eq1)
          then show ?thesis using 0 by fast
        qed 
      qed 
      done
      subgoal by simp  
      subgoal for x31 x32 x33
        apply(simp add: fresh_star_def fresh_Pair fresh_append)
        apply safe
        using less by force+
      subgoal for x41 x42 x43
        apply(simp add: fresh_star_def fresh_Pair fresh_append)
        apply safe
        using less by force+
      subgoal for x51 x52
        apply(simp add: fresh_star_def fresh_Pair fresh_append)
        apply safe
        using less by force+
      done
  qed
 

section \<open>Typing\<close>

subsection \<open>Substitution\<close>

nominal_function subst_ty :: "ty \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> ty" ("_[_ \<mapsto> _]\<^sub>\<tau>" [300, 0, 0] 300)
where
  "(Tvar X)[Y \<mapsto> T]\<^sub>\<tau> = (if X=Y then T else Tvar X)" 
| "Top[Y \<mapsto> T]\<^sub>\<tau> = Top"
| "atom x\<sharp>(Y,T) \<Longrightarrow> (Arrow x S\<^sub>1 S\<^sub>2)[Y \<mapsto> T]\<^sub>\<tau> = 
                (Arrow x (S\<^sub>1[Y \<mapsto> T]\<^sub>\<tau>) (S\<^sub>2[Y \<mapsto> T]\<^sub>\<tau>))"
| "atom X\<sharp>(Y,T) \<Longrightarrow> (\<forall>X<:B. T\<^sub>1)[Y \<mapsto> T]\<^sub>\<tau> = 
                (\<forall>X<:B[Y \<mapsto> T]\<^sub>\<tau>. T\<^sub>1[Y \<mapsto> T]\<^sub>\<tau>)"
| "(x \<triangleright> T\<^sub>1)[Y \<mapsto> T]\<^sub>\<tau> = (x \<triangleright> T\<^sub>1[Y \<mapsto> T]\<^sub>\<tau>)"
  apply simp_all
  subgoal by(simp add: eqvt_def subst_ty_graph_aux_def)
  subgoal premises prems for P x
  proof -
    obtain op Y T where x_expr: "x = (op,Y,T)" using prod_cases3 by blast 
    show ?thesis
      apply(rule ty.strong_exhaust[of "fst x" P "(Y,T)"]) 
      by(simp_all add: x_expr prems atom_vrs_def fresh_star_def)
  qed
  subgoal for x Y T S\<^sub>1 S\<^sub>2 xa Ya Ta S\<^sub>1' S\<^sub>2'
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
  subgoal for X Y T B T\<^sub>1 Xa Ya Ta Ba T\<^sub>1'
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
    done

nominal_termination (eqvt)
  by lexicographic_order
  
nominal_function subst_trm :: "trm \<Rightarrow> vrs \<Rightarrow> trm \<Rightarrow> trm"  ("_[_ \<mapsto> _]" [300, 0, 0] 300)
where
  "(Var x)[y \<mapsto> t] = (if x=y then t else (Var x))"
| "atom x\<sharp>(y,t) \<Longrightarrow> (Abs x t\<^sub>1 T)[y \<mapsto> t] = (Abs x (t\<^sub>1[y \<mapsto> t]) T)"
| "atom X\<sharp>(y,t) \<Longrightarrow> (\<lambda>X<:T. t\<^sub>1)[y \<mapsto> t] = (\<lambda>X<: T. t\<^sub>1[y \<mapsto> t])" 
| "(t1 \<cdot> t2)[y \<mapsto> t] = (t1[y \<mapsto> t]) \<cdot> (t2[y \<mapsto> t])"
| "(t\<^sub>1 \<cdot>\<^sub>\<tau> T)[y \<mapsto> t] = ((t\<^sub>1[y \<mapsto> t]) \<cdot>\<^sub>\<tau> T)"
  apply simp_all
  subgoal by(simp add: eqvt_def subst_trm_graph_aux_def)
  subgoal premises prems for P x
  proof -
    obtain op y t where x_expr: "x = (op,y,t)" using prod_cases3 by blast 
    show ?thesis
      apply(rule trm.strong_exhaust[of "fst x" P "(y,t)"]) 
      by(simp_all add: x_expr prems atom_vrs_def fresh_star_def)
  qed
  subgoal for x y t t\<^sub>1 T xa ya ta t\<^sub>1' Ta
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
  subgoal for X y t T t\<^sub>1 Xa ya ta Ta t\<^sub>1'
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
    done

nominal_termination (eqvt)
  by lexicographic_order

nominal_function subst_trm_ty :: "trm \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> trm"  ("_[_ \<mapsto>\<^sub>\<tau> _]" [300, 0, 0] 300)
where
  "(Var x)[Y \<mapsto>\<^sub>\<tau> T2] = Var x"
| "(t1 \<cdot> t2)[Y \<mapsto>\<^sub>\<tau> T2] = t1[Y \<mapsto>\<^sub>\<tau> T2] \<cdot> t2[Y \<mapsto>\<^sub>\<tau> T2]"
| "(t1 \<cdot>\<^sub>\<tau> T)[Y \<mapsto>\<^sub>\<tau> T2] = t1[Y \<mapsto>\<^sub>\<tau> T2] \<cdot>\<^sub>\<tau> T[Y \<mapsto> T2]\<^sub>\<tau>"
| "atom X\<sharp>(Y,T2) \<Longrightarrow> (\<lambda>X<:T. t)[Y \<mapsto>\<^sub>\<tau> T2] = (\<lambda>X<:T[Y \<mapsto> T2]\<^sub>\<tau>. t[Y \<mapsto>\<^sub>\<tau> T2])" 
| "atom x\<sharp>(Y,T2) \<Longrightarrow> (Abs x t T)[Y \<mapsto>\<^sub>\<tau> T2] = (Abs x (t[Y \<mapsto>\<^sub>\<tau> T2]) (T[Y \<mapsto> T2]\<^sub>\<tau>))"
  apply simp_all
  subgoal by(simp add: eqvt_def subst_trm_ty_graph_aux_def)
  subgoal premises prems for P x
  proof -
    obtain op y T where x_expr: "x = (op,y,T)" using prod_cases3 by blast 
    show ?thesis
      apply(rule trm.strong_exhaust[of "fst x" P "(y,T)"]) 
      by(simp_all add: x_expr prems atom_vrs_def fresh_star_def)
  qed
  subgoal for x y t t\<^sub>1 T xa ya ta t\<^sub>1' Ta
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
  subgoal for X y t T t\<^sub>1 Xa ya ta Ta t\<^sub>1'
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
    done

nominal_termination (eqvt)
  by lexicographic_order

definition cap_subst :: "vrs list \<Rightarrow> vrs \<Rightarrow> vrs list \<Rightarrow> vrs list" where
  "cap_subst C' y C = (if (y \<in> set C') then (removeAll y C') @ C else C')"

lemma cap_subst_eqvt[eqvt]:
  fixes T::"ty" and y::"vrs" and C C'::"vrs list"
  shows "p\<bullet>(cap_subst C' y C) = cap_subst (p\<bullet>C') (p\<bullet>y) (p\<bullet>C)"
  unfolding cap_subst_def
  by(simp split: if_splits)

lemma cap_subst_idemp: "set (cap_subst C y C) = set C"
  unfolding cap_subst_def by auto
  
lemma cap_subst_nil: "cap_subst [] y C = []"
  unfolding cap_subst_def by auto

nominal_function subst_cap :: "ty \<Rightarrow> vrs \<Rightarrow> vrs list \<Rightarrow> ty" ("_[_ \<mapsto> _]\<^sub>c" [300, 0, 0] 300)
where
  "(Tvar X)[y \<mapsto> C]\<^sub>c = Tvar X"
| "Top[y \<mapsto> C]\<^sub>c = Top"
| "atom x\<sharp>(y,C) \<Longrightarrow> (Arrow x S T)[y \<mapsto> C]\<^sub>c = (Arrow x (S[y \<mapsto> C]\<^sub>c) (T[y \<mapsto> C]\<^sub>c))"
| "atom X\<sharp>(y,C) \<Longrightarrow> (\<forall>X<:B. T\<^sub>1)[y \<mapsto> C]\<^sub>c = (\<forall>X<:B[y \<mapsto> C]\<^sub>c. T\<^sub>1[y \<mapsto> C]\<^sub>c)"
| "(C' \<triangleright> T\<^sub>1)[y \<mapsto> C]\<^sub>c = ((cap_subst C' y C) \<triangleright> (T\<^sub>1[y \<mapsto> C]\<^sub>c))"
  apply simp_all
  subgoal by(simp add: eqvt_def subst_cap_graph_aux_def)
  subgoal premises prems for P x
  proof -
    obtain op y C where x_expr: "x = (op,y,C)" using prod_cases3 by blast 
    show ?thesis
      apply(rule ty.strong_exhaust[of "fst x" P "(y,C)"]) 
      by(simp_all add: x_expr prems atom_vrs_def fresh_star_def)
  qed
  subgoal for x y t t\<^sub>1 T xa ya ta t\<^sub>1' Ta
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
  subgoal for X y t T t\<^sub>1 Xa ya ta Ta t\<^sub>1'
     apply(simp add: fresh_Pair eqvt_at_def)
      by (smt flip_fresh_fresh)+
    done

nominal_termination (eqvt)
  by lexicographic_order

nominal_function
  subst_tyb :: "binding \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> binding" ("_[_ \<mapsto> _]\<^sub>b" [100,100,100] 100)
where
  "(TVarB X U)[Y \<mapsto> T]\<^sub>b = TVarB X (U[Y \<mapsto> T]\<^sub>\<tau>)"
| "(VarB  X U)[Y \<mapsto> T]\<^sub>b =  VarB X (U[Y \<mapsto> T]\<^sub>\<tau>)"
  apply simp_all
  subgoal by(simp add: eqvt_def subst_tyb_graph_aux_def)
  subgoal premises prems for P x
  proof -
    obtain op y C where x_expr: "x = (op,y,C)" using prod_cases3 by blast 
    then show ?thesis
      apply(cases rule: binding.strong_exhaust[of "op" P])
      using prems by auto
  qed
done

nominal_termination (eqvt)
  by lexicographic_order

primrec subst_tyc :: "env \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> env" ("_[_ \<mapsto> _]\<^sub>e" [100,100,100] 100) where
  "([])[Y \<mapsto> T]\<^sub>e= []"
| "(B#\<Gamma>)[Y \<mapsto> T]\<^sub>e = (B[Y \<mapsto> T]\<^sub>b)#(\<Gamma>[Y \<mapsto> T]\<^sub>e)"

subsection \<open>Subtyping\<close>

lemma listmem_eqvt [eqvt]:
  fixes x :: vrs
  shows "p \<bullet> (ListMem x l) = ListMem (p \<bullet> x) (p \<bullet> l)"
  by(induct l,auto simp add: ListMem_iff)

inductive 
  subtype_of :: "env \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"   ("_\<turnstile>_<:_" [100,100,100] 100)
  where
  SA_refl[intro]:      "\<turnstile> \<Gamma> ok \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
| SA_trans[intro]:     "\<lbrakk>\<Gamma> \<turnstile> R <: S; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> R <: T"
| SA_TVar[intro]:      "\<lbrakk>\<turnstile> \<Gamma> ok; ListMem X (ty_dom \<Gamma>); extract_subtype X \<Gamma> = (Some T, E')\<rbrakk>\<Longrightarrow> 
                         \<Gamma> \<turnstile> Tvar X <: T"
| SA_Top[intro]:       "\<lbrakk>\<turnstile> \<Gamma> ok; cv T \<Gamma> True = []\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T <: Top"
| SA_arrow[intro]:     "\<lbrakk>\<Gamma> \<turnstile> S\<^sub>2 <: S\<^sub>1; ((VarB x S\<^sub>2) # \<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>2\<rbrakk> \<Longrightarrow> 
                         \<Gamma> \<turnstile> (Arrow x S\<^sub>1 T\<^sub>1) <: (Arrow x S\<^sub>2 T\<^sub>2)" 
| SA_all[intro]:       "\<lbrakk>\<Gamma> \<turnstile> S\<^sub>2 <: S\<^sub>1; ((TVarB X S\<^sub>2) # \<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>2\<rbrakk> \<Longrightarrow> 
                        \<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. T\<^sub>1) <: (\<forall>X<:S\<^sub>2. T\<^sub>2)"
| SA_captr[intro]:     "\<turnstile> \<Gamma> ok \<Longrightarrow> \<Gamma> \<turnstile> T <: (C \<triangleright> T)"
| SA_capti[intro]:     "\<lbrakk>\<Gamma> \<turnstile> S <: T; set C \<subseteq> set (cv T \<Gamma> True)\<rbrakk> \<Longrightarrow> 
                         \<Gamma> \<turnstile> (C \<triangleright> S) <: T"

equivariance subtype_of

nominal_inductive subtype_of done

inductive_cases subE:
  "\<Gamma> \<turnstile> T <: Tvar X"

lemma subtyping_ok:
  assumes "\<Gamma> \<turnstile> S <: T"
  shows   "\<turnstile> \<Gamma> ok"
  using assms 
  apply (induct) 
  by simp_all

subsection \<open>Typing\<close>

definition removeAllList :: "vrs list \<Rightarrow> vrs list \<Rightarrow> vrs list" where
"removeAllList to_remove from' = 
   fold removeAll to_remove from'"

lemma removeAllList_eqvt[eqvt]:
  shows "p\<bullet>(removeAllList toRem from') = 
          removeAllList (p\<bullet>toRem) (p\<bullet>from')"
  unfolding removeAllList_def
  by(induction toRem arbitrary: from') auto

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [60,60,60] 60) 
where
  T_Var[intro]: "\<lbrakk> VarB x T \<in> set \<Gamma>; \<turnstile> \<Gamma> ok\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| T_Sub[intro]: "\<lbrakk> \<Gamma> \<turnstile> t: S; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> t : T"
| T_App[intro]: "\<lbrakk> \<Gamma> \<turnstile> t : (C \<triangleright> Arrow x R T); 
                   \<Gamma> \<turnstile> s : S;
                   \<Gamma> \<turnstile> S <: R[x \<mapsto> (cv S \<Gamma> True)]\<^sub>c \<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> t \<cdot> s : T[x \<mapsto> (cv S \<Gamma> True)]\<^sub>c"
| T_TApp[intro]:"\<lbrakk> atom X \<sharp> (\<Gamma>,t,S);
                   \<Gamma> \<turnstile> t : (C \<triangleright> (Forall X T R)); 
                   \<Gamma>; []; [] \<turnstile> S wf;
                   \<Gamma> \<turnstile> S <: R[X \<mapsto> (cv S \<Gamma> True)]\<^sub>c\<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> t \<cdot>\<^sub>\<tau> S : ((T[X \<mapsto> S]\<^sub>\<tau>)[X \<mapsto> (cv S \<Gamma> True)]\<^sub>c)" 
| T_Abs[intro]: "\<lbrakk> VarB x S # \<Gamma> \<turnstile> t : T;
                   \<Gamma> ; [] ; [VarB x S] \<turnstile> S wf \<rbrakk> \<Longrightarrow> 
                  \<Gamma> \<turnstile> (Abs x t T) : 
                      ((removeAllList (cv_trm t E) 
                                     (cv T E True)) \<triangleright> 
                        (Arrow x S T))"
| T_TAbs[intro]: "\<lbrakk> TVarB X S # \<Gamma> \<turnstile> t : T;
                   \<Gamma> ; [] ; [TVarB X S] \<turnstile> S wf \<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> (TAbs X t T) : 
                      ((removeAllList (cv_trm t E) 
                                     (cv T E True)) \<triangleright> 
                        (Arrow X S T))"

equivariance typing
nominal_inductive typing done 

lemma typing_ok:
  assumes "\<Gamma> \<turnstile> t : T"
  shows   "\<turnstile> \<Gamma> ok"
  using assms 
  apply (induct) 
  using valid_rel.cases by auto

section \<open>Inversion lemmas\<close>

section \<open>Substitution lemma\<close>

section \<open>Evaluation\<close>

inductive 
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longmapsto> _" [60,60] 60)
where
  E_TApp [intro]: "t \<longmapsto> t' \<Longrightarrow> (t \<cdot>\<^sub>\<tau> T) \<longmapsto> (t' \<cdot>\<^sub>\<tau> T)"
| E_App1 [intro]: "t \<longmapsto> t' \<Longrightarrow> t \<cdot> u \<longmapsto> t' \<cdot> u"
| E_App2 [intro]: "\<lbrakk> is_val v; t \<longmapsto> t' \<rbrakk> \<Longrightarrow> v \<cdot> t \<longmapsto> v \<cdot> t'"
| E_Abs         : "\<lbrakk> atom x \<sharp> v; is_val v \<rbrakk> \<Longrightarrow> (Abs x t T) \<cdot> v \<longmapsto> t[x \<mapsto> v]"
| E_TAbs        : "atom X \<sharp> T \<Longrightarrow> ((TAbs X t B) \<cdot>\<^sub>\<tau> T) \<longmapsto> (t[X \<mapsto>\<^sub>\<tau> T])"

equivariance eval
nominal_inductive eval done

section \<open>Term subtyping lemma\<close>

lemma fresh_capsubst:
  assumes "atom x \<sharp> T"
  shows "T = T[x \<mapsto> S]\<^sub>c"
  using assms
  apply(nominal_induct T avoiding: x S rule: ty.strong_induct)
  by(simp_all add: fresh_at_base(2) cap_subst_def fresh_vrs_list)+

lemma cv_skip_trm_bind: "cv T (VarB x R # \<Gamma>) b = cv T \<Gamma> b"
  apply(nominal_induct T avoiding: x R \<Gamma> 
      arbitrary: b rule: ty.strong_induct)
      apply simp_all
  subgoal for x1a x2 x3 x R \<Gamma> b
    apply(subgoal_tac "atom x1a \<sharp> (VarB x R # \<Gamma>)")
    by(simp_all add: fresh_Cons)
  subgoal for x1a x2 x3 x R \<Gamma> b
    apply(subgoal_tac "atom x1a \<sharp> (VarB x R # \<Gamma>)")
    by(simp_all add: fresh_Cons)
  done

lemma cv_cap_subst:
  assumes "atom x \<sharp> cv T \<Gamma> b"
  shows "cv (T[x \<mapsto> C]\<^sub>c) \<Gamma> b = cv T \<Gamma> b"
  using assms
  apply(nominal_induct T avoiding: x C \<Gamma> 
        arbitrary: b rule: ty.strong_induct)
  subgoal for x xa C \<Gamma> by auto
  subgoal for x C \<Gamma> by simp
  subgoal for x1a x2 x3 x C \<Gamma> b
    apply(simp add: fresh_append)
    apply(rule arg_cong2[of _ _ _ _ append];
          rule arg_cong2[of _ _ _ _ removeAll]; 
          clarify)
     apply(drule fresh_removeAll')
    using fresh_atom fresh_atom_at_base apply blast
     apply(drule fresh_removeAll')
    using fresh_at_base(2) fresh_removeAll' by blast
  subgoal for x1a x2 x3 x C \<Gamma> b
    apply(simp add: fresh_append)
    apply safe
    apply(drule fresh_removeAll')
    apply(rule arg_cong2[of _ _ _ _ removeAll])
     apply simp
    by(simp add: fresh_at_base(2))
  subgoal for x1a x2 x C \<Gamma> b
    apply(simp)
    apply(cases "b")
     apply(simp_all add: fresh_append cap_subst_def, safe)
    using fresh_vrs_list by blast
  done

lemma fresh_lookup:
  assumes "atom xa \<sharp> ty_dom \<Gamma>"
  shows "cv (Tvar xa) \<Gamma> b = []"
  using assms
  apply(induction \<Gamma>)
   apply simp
  subgoal for a \<Gamma>
    apply(cases a rule: binding.strong_exhaust)
     apply force
    apply(simp only: ty_dom.simps tyvrs_of.simps 
                      fresh_append fresh_Cons fresh_Nil)
    apply(simp)
    apply(cases "b")
     apply safe
    by argo
  done

lemma fresh_type_env:
  assumes "atom x \<sharp> \<Gamma>" "atom x \<sharp> T"
  shows "x \<notin> set (cv T \<Gamma> b)"
  using assms
  apply(induction "(length \<Gamma>, size T)" 
        arbitrary: T \<Gamma> b rule: less_induct)
  subgoal for T \<Gamma> b
    apply(cases T rule: ty.strong_exhaust[of _ _ "\<Gamma>"])
    subgoal for x1
      apply(simp only: cv.simps split: if_splits prod.splits option.splits)
        apply safe
         apply simp_all
      by (metis extract_dec_length extract_some fresh_append fresh_extract)
    subgoal by simp
    subgoal for x31 x32 x33
      by(auto simp add: fresh_star_def)
    subgoal
      by(auto simp add: fresh_star_def)
    subgoal for x51 x52 
      apply simp
      using fresh_vrs_list by blast
    done
  done

lemma fresh_lookup':
  assumes "atom xa \<sharp> \<Gamma>"
  shows "xa \<notin> set (cv (Tvar x) \<Gamma> b)"
  using assms
  apply(simp only: cv.simps split: if_splits prod.splits option.splits)
  apply safe
     apply simp_all
  by (metis extract_some fresh_append fresh_extract fresh_type_env)
    
lemma cv_cap_subst':
  assumes "x \<in> set (cv T \<Gamma> b)" "atom x \<sharp> \<Gamma>"
  shows "set C \<subseteq> set (cv (T[x \<mapsto> C]\<^sub>c) \<Gamma> b)"
  using assms
  apply(nominal_induct T avoiding: \<Gamma> x C
        arbitrary: b rule: ty.strong_induct)
  subgoal for xa   
    using fresh_lookup' by blast
  subgoal by simp
  subgoal for x1a x2 x3 \<Gamma> x C
    apply simp
    apply safe
           apply simp_all
    using fresh_vrs_list by blast+
  subgoal for x1a x2 x3 \<Gamma> y C b
    apply simp
    apply safe
       apply(simp_all add: fresh_vrs_list)+
    by blast+
  subgoal for x1a x2 \<Gamma> x C b
    apply(simp split: if_splits)
    apply safe
     apply (simp add: cap_subst_def)
    by blast
  done

lemma cv_cap_subst_mono_elem:
  assumes "x \<in> set (cv T \<Gamma> b)" "x \<noteq> y"
  shows "x \<in> set (cv (T[y \<mapsto> C]\<^sub>c) \<Gamma> b)"
  using assms
  apply(nominal_induct T avoiding: \<Gamma> y C
        arbitrary: b rule: ty.strong_induct)
  subgoal for x \<Gamma> y C b  
    using subst_cap.simps(1) by presburger
  subgoal by simp
  subgoal for x1a x2 x3 \<Gamma> y C b by auto
  subgoal for x1a x2 x3 \<Gamma> y C b by auto
  subgoal for x1a x2 \<Gamma> x C b 
    apply(simp split: if_splits)
    apply safe
     apply (simp add: cap_subst_def)
    by blast
  done

lemma cv_cap_subst_mono:
  assumes "set C \<subseteq> set (cv T \<Gamma> b)" "y \<notin> set C"
  shows "set C \<subseteq> set (cv (T[y \<mapsto> C]\<^sub>c) \<Gamma> b)"
  using assms cv_cap_subst_mono_elem by force

nominal_function
  "cap_subst_bind" :: "binding \<Rightarrow> vrs \<Rightarrow> vrs list \<Rightarrow> binding"
where
  "cap_subst_bind (VarB y B) x C  = (VarB y (B[x \<mapsto> C]\<^sub>c))"
| "cap_subst_bind (TVarB Y B) x C = (TVarB Y (B[x \<mapsto> C]\<^sub>c))"
      using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal 
    by(simp add: eqvt_def cap_subst_bind_graph_aux_def split: option.splits prod.splits)
  by (metis binding.strong_exhaust prod.exhaust_sel)
 
nominal_termination (eqvt) 
  by lexicographic_order
  
primrec
  "cap_subst_bind_list" :: "env \<Rightarrow> vrs \<Rightarrow> vrs list \<Rightarrow> env"
  ("_[_ \<mapsto> _]\<^sup>c" [300, 0, 0] 300)
where
  "cap_subst_bind_list [] x C = []"
| "cap_subst_bind_list (b#\<Gamma>) x C = (cap_subst_bind b x C) # (cap_subst_bind_list \<Gamma> x C)" 

lemma fresh_type_cap_subst:
  assumes "atom X \<sharp> T" "atom X \<sharp> C"
  shows "atom X \<sharp> T[x \<mapsto> C]\<^sub>c"
  using assms
  apply(nominal_induct T 
        avoiding: x C
        rule: ty.strong_induct)
      apply simp_all
    apply presburger
   apply blast
  apply(simp add: cap_subst_def fresh_append)
  by (metis cap_subst_def cap_subst_idemp fresh_append fresh_set)
  
lemma fresh_bind_list_cap_subst:
  assumes "atom X \<sharp> \<Delta>" "atom X \<sharp> C"
  shows "atom X \<sharp> \<Delta>[x \<mapsto> C]\<^sup>c"
  using assms
  apply(induction \<Delta>)
   apply(simp_all add: fresh_Nil fresh_Cons)
  subgoal for a \<Delta>
    apply(cases "a" rule: binding.strong_exhaust)
     apply simp_all
    using fresh_type_cap_subst by blast+
  done

lemma
  assumes " \<turnstile> (\<Delta> @ VarB x R # \<Gamma>) ok" 
  shows "\<turnstile> (\<Delta>[x \<mapsto> C]\<^sup>c @ \<Gamma>) ok"
  using assms
  apply(nominal_induct "\<Delta> @ VarB x R # \<Gamma>" 
        avoiding: C
        arbitrary: \<Delta>
        rule: valid_rel.strong_induct)
  subgoal by simp
  subgoal premises prems for \<Gamma>' X U C \<Delta>
  proof -
    have "\<Delta> \<noteq> []"
      using prems(6) by auto
    then obtain \<Delta>' where d_expr: "\<Delta> = TVarB X U # \<Delta>'" 
      using prems 
      by (metis append_eq_Cons_conv)
    show ?thesis
      thm prems
      apply(simp add: d_expr)
      apply(rule valid_rel.valid_consT)
      using d_expr prems(2) prems(6) apply auto[1]
        apply(simp add: fresh_append)
      
    then have "\<Gamma>' = \<Delta>' @ VarB x R # \<Gamma>"
      using prems(6) by auto
    then have "\<turnstile> (\<Delta>'[x \<mapsto> C]\<^sup>c @ \<Gamma>) ok" 
      using prems by blast
    have "atom X \<sharp> \<Gamma>"
      using \<open>\<Gamma>' = \<Delta>' @ VarB x R # \<Gamma>\<close> prems(3)
      by (simp add: fresh_append fresh_Cons)
    then have "atom X \<sharp> set(trm_dom \<Gamma> @ ty_dom \<Gamma>)" 
      using fresh_append fresh_dom(1) fresh_dom(2) fresh_set by blast
    then have "atom X \<sharp> C"
      using prems(7) 
      by (smt List.finite_set fresh_def imageE image_eqI subset_iff supp_finite_set_at_base supp_set)
    show ?thesis 
      apply(simp add: d_expr)
      apply(rule valid_rel.valid_consT)
         apply (simp add: \<open>\<turnstile> (\<Delta>'[x \<mapsto> C]\<^sup>c @ \<Gamma>) ok\<close>)
        apply(simp add: fresh_append, safe)

      using fresh_bind_list_cap_subst 

      using prems
        defer 1
      defer 1
      
      sorry
  qed
  subgoal for \<Gamma>' xa T \<Delta>

    sorry
  oops


lemma subst_cap_isotone:
  assumes a: "(\<Delta> @ VarB x R # \<Gamma>) \<turnstile> S <: T" 
  assumes b: "\<turnstile> (\<Delta> @ VarB x R # \<Gamma>) ok" 
  assumes c: "atom x \<sharp> C"
  shows "(\<Delta>[x \<mapsto> C]\<^sup>c @ \<Gamma>) \<turnstile> S[x \<mapsto> C]\<^sub>c <: T[x \<mapsto> C]\<^sub>c" 
  using a c
proof(nominal_induct "\<Delta> @ VarB x R # \<Gamma>" S T 
      avoiding: 
      arbitrary: \<Delta>
      rule: subtype_of.strong_induct)
  case (SA_refl T)
  then have "\<turnstile> \<Gamma> ok"
    using validE_append by fast
  show ?case     
    apply(rule subtype_of.SA_refl) 
    sorry
next
  case (SA_trans R S T)
  then show ?case by auto
next
  case (SA_TVar X T E')
  have "\<turnstile> (VarB x R # \<Gamma>) ok"
    using SA_TVar.hyps(1) validE_append by blast
  then have "atom x \<sharp> T"
    using SA_TVar.hyps(3) fresh_extract sorry
  then have "T[x \<mapsto> C]\<^sub>c = T"
    using fresh_capsubst by auto
  then show ?case
    using SA_TVar.hyps by auto
next
  case (SA_Top T)
  then show ?case 
    apply simp
    apply(rule subtype_of.SA_Top)
    using SA_Top apply blast
    apply(subst cv_cap_subst)
     apply (simp add: cv_skip_trm_bind fresh_Nil)
    apply(subst (asm) cv_skip_trm_bind)
    by auto
next
  case (SA_arrow S\<^sub>2 S\<^sub>1 y T\<^sub>1 T\<^sub>2)
  have 1: "atom x \<sharp> y"
    sorry
  have 2: "atom y \<sharp> C"   
    sorry
  have "(VarB y S\<^sub>2 # \<Delta>)[x \<mapsto> C]\<^sup>c = VarB y (S\<^sub>2[x \<mapsto> C]\<^sub>c) # \<Delta>[x \<mapsto> C]\<^sup>c"
    by simp

  from 1 2 SA_arrow show ?case (* (y: S\<^sub>1) \<rightarrow> T\<^sub>1 *)
    using SA_arrow
    apply simp    
    apply(rule subtype_of.SA_arrow)
     apply assumption
    by force
next
  case (SA_all S\<^sub>2 S\<^sub>1 x T\<^sub>1 T\<^sub>2 X)
  then show ?case 
    sorry
next
  case (SA_captr T)
  then have "\<turnstile> \<Gamma> ok"
    using validE_append by fast
  then show ?case 
    apply simp
    apply(rule subtype_of.SA_captr)
    by auto
next
  case (SA_capti S T Ca)
  then show ?case 
    apply simp
    apply(rule subtype_of.SA_capti)
     apply fast
    unfolding cap_subst_def
    apply(simp only: split: if_splits)
    apply safe
     apply(simp add: cv_skip_trm_bind)
    sorry
(*
     apply (meson cv_cap_subst' cv_cap_subst_mono_elem subset_code(1) subtyping_ok validE(2))
    by (metis cv_cap_subst_mono_elem cv_skip_trm_bind subsetD) *)
qed

theorem subst_type: 
  assumes "VarB x R # \<Gamma> \<turnstile> t : T" "\<Gamma> \<turnstile> s : S"
          "\<Gamma> \<turnstile> S <: R[x \<mapsto> cv S \<Gamma> True]\<^sub>c"
  shows "\<Gamma> \<turnstile> t[x \<mapsto> s] : T[x \<mapsto> cv S \<Gamma> True]\<^sub>c" 
  using assms
proof (nominal_induct "VarB x R # \<Gamma>" t T 
       avoiding: x s arbitrary: rule: typing.strong_induct)
  case (T_Var y T)
  then show ?case 
  proof(cases "x = y")
    case True
    then have eq: "T = R" 
      using T_Var.hyps(1) T_Var.hyps(2) uniqueness_of_ctxt' by force
    show ?thesis 
      apply(simp add: True eq)
      using T_Var.prems(1) T_Var.prems(2) True by blast
  next
    case False
    have "atom x \<sharp> T" 
      by (metis False T_Var.hyps(1) T_Var.hyps(2) binding.eq_iff(1) binding.fresh(1) fresh_Cons fresh_append in_set_conv_decomp set_ConsD validE(2))
    then have t: "T = T[x \<mapsto> cv S \<Gamma> True]\<^sub>c"
      using fresh_capsubst by blast
    show ?thesis
      apply(simp add: False t[symmetric])
      using False T_Var.hyps(1) assms(2) typing_ok by auto
  qed
next
  case (T_Sub t R' T')

  show ?case 
    apply(rule typing.T_Sub)
     apply(rule T_Sub)+
    using T_Sub 
    (*using subst_cap_isotone[OF T_Sub(3), of "cv S \<Gamma> True"]
    using typing_ok by blast*)
    sorry
next
  case (T_App t C x Ra T s Sa xa sa)
  then show ?case 
    apply simp
    apply(rule typing.T_App)
    
    sorry
next
  case (T_TApp X t S C T R x)
  then show ?case 
    apply simp
    sorry
next
  case (T_Abs x S t T E)
  then show ?case sorry
next
  case (T_TAbs X S t T E)
  then show ?case sorry
qed
 


section \<open>Soundness\<close>

lemma abs_eq_binder:
  assumes "\<Gamma> \<turnstile> (\<lambda>y:Q. q): (C \<triangleright> (Arrow x R T))" 
  obtains z where
    "VarB z ((x \<leftrightarrow> z) \<bullet> R) # \<Gamma> \<turnstile> (y \<leftrightarrow> z) \<bullet> q : ((x \<leftrightarrow> z) \<bullet> T)"
    "\<Gamma> ; [] ; [VarB z ((x \<leftrightarrow> z) \<bullet> R)] \<turnstile> ((x \<leftrightarrow> z) \<bullet> R) wf"
    "atom z \<sharp> (s\<^sub>1::trm)" 
  using assms
  apply(cases \<Gamma> "\<lambda>y:Q. q" "C \<triangleright> (Arrow x R T)" rule: typing.cases)
  subgoal for S
    
    sorry
  subgoal for xa S t Ta E
  proof -
    assume 1: "[[atom y]]lst. (q, Q) = [[atom xa]]lst. (t, Ta)"
              "[[atom x]]lst. (R, T) = [[atom xa]]lst. (S, Ta)"
    assume 2: "VarB xa S # \<Gamma> \<turnstile> t : Ta"
    assume 3: "(\<And>z. VarB z ((x \<leftrightarrow> z) \<bullet> R) # \<Gamma> \<turnstile> (y \<leftrightarrow> z) \<bullet> q : (x \<leftrightarrow> z) \<bullet> T \<Longrightarrow>
          \<Gamma> ; [] ; [VarB z ((x \<leftrightarrow> z) \<bullet> R)] \<turnstile> (x \<leftrightarrow> z) \<bullet> R wf \<Longrightarrow>
          atom z \<sharp> s\<^sub>1 \<Longrightarrow> thesis)" 
    assume 4: "\<Gamma> ; [] ; [VarB xa S] \<turnstile> S wf" 

    obtain z :: vrs where fr: "atom z \<sharp> (\<Gamma>,x,y,xa,q,Q,R,T,t,Ta,S,s\<^sub>1)"
      by(blast intro: obtain_fresh)
    have "atom xa \<sharp> \<Gamma>" 
      using "2" typing_ok by blast
    have o1: "(xa \<leftrightarrow> z) \<bullet> \<Gamma> = \<Gamma>"
      using \<open>atom xa \<sharp> \<Gamma>\<close> flip_fresh_fresh fr fresh_PairD(1) by blast
    have o2: "(x \<leftrightarrow> z) \<bullet> R = (xa \<leftrightarrow> z) \<bullet> S" 
             "(x \<leftrightarrow> z) \<bullet> T = (xa \<leftrightarrow> z) \<bullet> Ta" 
             "(y \<leftrightarrow> z) \<bullet> q = (xa \<leftrightarrow> z) \<bullet> t" 
        apply -   
        apply(all \<open>subst Abs1_eq_iff_fresh(3)[symmetric]\<close>)
      apply(simp add: fresh_Pair fr)
      apply(blast intro: 1 bind_pair_proj_1)
      apply(simp add: fresh_Pair fr)
      apply(blast intro: 1 bind_pair_proj_2)
      apply(simp add: fresh_Pair fr)
      by(blast intro: 1 bind_pair_proj_1)

    have 5: "VarB z ((x \<leftrightarrow> z) \<bullet> R) # \<Gamma> \<turnstile> 
           (y \<leftrightarrow> z) \<bullet> q : (x \<leftrightarrow> z) \<bullet> T" 
      using typing.eqvt[OF 2, of "(xa \<leftrightarrow> z)"]
      by(simp add: o1 o2)
    have 6: "\<Gamma> ; [] ; [VarB z ((x \<leftrightarrow> z) \<bullet> R)] \<turnstile> ((x \<leftrightarrow> z) \<bullet> R) wf"
      using valid_ty.eqvt[OF 4, of "(xa \<leftrightarrow> z)"]
      by(simp add: o1 o2)
    have 7: "atom z \<sharp> s\<^sub>1"
      using fr by(simp add: fresh_Pair)

    show ?thesis
      using 3 5 6 7 by fast
  qed
  done

theorem preservation: 
  assumes "\<Gamma> \<turnstile> t : T" "t \<longmapsto> t'"
  shows "\<Gamma> \<turnstile> t' : T" 
  using assms
proof (nominal_induct avoiding: t t' rule: typing.strong_induct)
  case (T_Var x T \<Gamma>)
  then show ?case using eval.cases by force
next   
  case (T_App \<Gamma> t\<^sub>1 C x R T s\<^sub>1 S t')
  then show ?case 
  proof -
    from \<open>t\<^sub>1 \<cdot> s\<^sub>1 \<longmapsto> t'\<close> show ?case
    proof(cases rule: eval.cases)
      case (E_Abs y q Q) 
      have "\<Gamma> \<turnstile> (\<lambda>y:Q. q): (C \<triangleright> (Arrow x R T))" 
        using E_Abs(1) T_App by auto
      then obtain z where r:
        "VarB z ((x \<leftrightarrow> z) \<bullet> R) # \<Gamma> \<turnstile> (y \<leftrightarrow> z) \<bullet> q : ((x \<leftrightarrow> z) \<bullet> T)"
        "\<Gamma> ; [] ; [VarB z ((x \<leftrightarrow> z) \<bullet> R)] \<turnstile> ((x \<leftrightarrow> z) \<bullet> R) wf"
        "atom z \<sharp> s\<^sub>1"
        using abs_eq_binder by blast
      define Q' q' R' T' where swap_def:
        "Q' = (y \<leftrightarrow> z) \<bullet> Q" "q' = (y \<leftrightarrow> z) \<bullet> q"
        "R' = (x \<leftrightarrow> z) \<bullet> R" "T' = (x \<leftrightarrow> z) \<bullet> T"
      then have "VarB z R' # \<Gamma> \<turnstile> q' : T'" 
                "(y \<leftrightarrow> z) \<bullet> q[y \<mapsto> s\<^sub>1] = q'[z \<mapsto> s\<^sub>1]"
        using r(1) apply blast
        unfolding swap_def 
        by (simp add: flip_fresh_fresh local.E_Abs(3) r(3))
      have "(x \<leftrightarrow> z) \<bullet> T[x \<mapsto> cv S \<Gamma> True]\<^sub>c =
            T'[z \<mapsto> cv S \<Gamma> True]\<^sub>c" 
        sorry
      thm subst_type
      show ?thesis 
        apply(simp add: E_Abs)

      sorry            
    next
      case (E_App1 t\<^sub>1')
      then show ?thesis 
        apply(simp add: E_App1)
        apply(intro typing.T_App T_App E_App1)+
          apply(rule T_App)
          apply(rule E_App1)
        by(rule T_App)+
    next
      case (E_App2 s\<^sub>1')    
      show ?thesis 
        apply(simp add: E_App2)
        apply(rule typing.T_App)
          apply(rule T_App)
         apply(rule T_App)
         apply(rule E_App2)
        by(rule T_App) 
    qed
  qed
next
  case (T_TApp X \<Gamma> t S C T R x ta t')
  show ?case 
    using \<open>t \<cdot>\<^sub>\<tau> S \<longmapsto> t'\<close>
    apply(cases rule: eval.cases)
    subgoal for ta'
      using T_TApp
      apply simp
      apply(rule typing.T_TApp)
         apply(simp add: fresh_Pair)
         defer 1
         apply blast
      apply blast 
        
    subgoal for Xa ta B
      apply simp
    sorry
next
  case (T_Abs x S \<Gamma> t T E)
  then show ?case using eval.cases by fastforce
next
  case (T_TAbs X S \<Gamma> t T E)
  then show ?case using eval.cases by fastforce
next
  case (T_Sub \<Gamma> t S T)
  then show ?case using eval.cases by fastforce
qed

end
