theory CaptureCalculusSub_Nominal2
  imports "Nominal2.Nominal2" 
          "HOL-Library.Rewrite"
          "HOL-Library.FSet"
          "HOL-Library.Product_Lexorder"
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
  shows "(supp (ty_dom  \<Gamma>)) = set (map atom (ty_dom  \<Gamma>))"
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
  using a
  apply(induct \<Gamma>)
  by (auto simp add: fresh_Nil fresh_Cons fresh_append tyvrs_fresh(1))

subsection \<open>Type ok\<close>

inductive
  valid_ty :: "env \<Rightarrow> env \<Rightarrow> ty \<Rightarrow> bool" ("_ ; _ \<turnstile> _ wf" [100,100,100] 100)
where
  tvar_wf[simp]:   "X \<in> set (ty_dom E\<^sub>1) \<Longrightarrow> E\<^sub>1; E\<^sub>2 \<turnstile> (Tvar X) wf"
| top_wf[simp]: "E\<^sub>1; E\<^sub>2 \<turnstile> Top wf"
| fun_wf[simp]: "\<lbrakk>E\<^sub>1; (VarB x S # E\<^sub>2) \<turnstile> S wf; 
                  (VarB x S # E1); E\<^sub>2 \<turnstile> T wf\<rbrakk> \<Longrightarrow> 
                  E\<^sub>1; E\<^sub>2 \<turnstile> (\<forall>X<:S. T) wf"
| tfun_wf[simp]: "\<lbrakk>E\<^sub>1; (TVarB X S # E\<^sub>2) \<turnstile> S wf; 
                  (TVarB X S # E1); E\<^sub>2 \<turnstile> T wf\<rbrakk> \<Longrightarrow> 
                  E\<^sub>1; E\<^sub>2 \<turnstile> (\<forall>X<:S. T) wf"
| capt_wf[simp]: "\<lbrakk>\<forall> X \<in> set C. X \<in> set (cv (Some (Tvar X)) (E\<^sub>1 @ E\<^sub>2) True);
                   E1; E\<^sub>2 \<turnstile> T wf\<rbrakk> \<Longrightarrow> 
                  E\<^sub>1; E\<^sub>2 \<turnstile> (C \<triangleright> T) wf"

equivariance valid_ty

nominal_inductive valid_ty done

subsection \<open>Environment ok\<close>

definition "closed_in" :: "ty \<Rightarrow> env \<Rightarrow> bool" ("_ closed'_in _" [100,100] 100) where
  "S closed_in \<Gamma> \<equiv> (supp S)\<subseteq> set (map atom (ty_dom \<Gamma>))"

lemma closed_in_eqvt[eqvt]:
  assumes "S closed_in \<Gamma>" 
  shows "(p\<bullet>S) closed_in (p\<bullet>\<Gamma>)" 
proof -
  from assms have "p\<bullet>(S closed_in \<Gamma>)" 
    by auto
  then show "(p\<bullet>S) closed_in (p\<bullet>\<Gamma>)" 
    by (simp add: closed_in_def)+
qed

inductive
  valid_rel :: "env \<Rightarrow> bool" ("\<turnstile> _ ok" [100] 100)
where
  valid_nil[simp]:   "\<turnstile> [] ok"
| valid_consT[simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; atom X\<sharp>(ty_dom  \<Gamma>); U closed_in \<Gamma>\<rbrakk>  \<Longrightarrow>  
                      \<turnstile> (TVarB X U#\<Gamma>) ok"
| valid_cons [simp]: "\<lbrakk>\<turnstile> \<Gamma> ok; atom x\<sharp>(trm_dom \<Gamma>); T closed_in \<Gamma>\<rbrakk>  \<Longrightarrow>  
                      \<turnstile> (VarB  x T#\<Gamma>) ok"

equivariance valid_rel
nominal_inductive valid_rel done

inductive_cases validE[elim]:
  "\<turnstile> (TVarB X U#\<Gamma>) ok" 
  "\<turnstile> (VarB x T#\<Gamma>) ok" 
  "\<turnstile> (b#\<Gamma>) ok" 

lemma ok_closed:
  assumes "\<turnstile> \<Gamma> ok"
  shows "VarB x T \<in> set \<Gamma> \<Longrightarrow> T closed_in \<Gamma>"
  and   "TVarB X T \<in> set \<Gamma> \<Longrightarrow> T closed_in \<Gamma>"
  using assms
  apply(induction rule: valid_rel.induct)
  by(auto simp add: closed_in_def)

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
  ultimately show "T=S" by auto
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
  ultimately show "T=S" by auto
qed auto

subsection \<open>Auxiliary functions\<close>

lemma fresh_removeAll:
  "(atom x) \<sharp> removeAll x list" 
  apply(induction list)
  by(auto simp add: fresh_Nil fresh_Cons)

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

primrec extract_subtype :: "vrs \<Rightarrow> env \<Rightarrow> ty option" where
  "extract_subtype x [] = (None::ty option)"
| "extract_subtype x (b # bs) = 
    (case (extract_subtype_b x b) of
      None \<Rightarrow> extract_subtype x bs
    | Some T \<Rightarrow> Some T)
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
  "extract_subtype x E = Some T \<Longrightarrow>
       (TVarB x T \<in> set E)"
   apply(induction E)
  by(simp_all add: extract_subtype_b_iff split: option.splits)

lemma extract_subtype_if_some:
  "(TVarB x T \<in> set E) \<Longrightarrow>
     (\<exists> B. extract_subtype x E = Some B)"
  apply(induction E)
  by(auto split: option.splits)

lemma extract_subtype_iff:
  assumes "\<turnstile> E ok"
  shows "extract_subtype x E = Some T \<longleftrightarrow> (TVarB x T \<in> set E)"
proof safe
  assume 1: "TVarB x T \<in> set E"
  show "extract_subtype x E = Some T"
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

lemma extraction_monotonic:
  assumes "set E \<subseteq> set E'"
          "extract_subtype x E = Some T"         
  shows "\<exists> Q. extract_subtype x E' = Some Q"
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

lemma extract_fresh_none:
  assumes "atom x \<sharp> ty_dom \<Gamma>"
  shows "extract_subtype x \<Gamma> = None"
proof(rule ccontr)
  assume "extract_subtype x \<Gamma> \<noteq> None"
  then obtain T where "extract_subtype x \<Gamma> = Some T" by blast
  then have "TVarB x T \<in> set \<Gamma>"
    using extract_subtype_if by blast
  then have "\<not> atom x \<sharp> \<Gamma>"
    by (metis binding.fresh(2) fresh_Cons fresh_at_base(2) fresh_set insert_absorb list.set(2))
  then have "\<not> atom x \<sharp> ty_dom \<Gamma>"
    by (metis \<open>TVarB x T \<in> set \<Gamma>\<close> fresh_Cons fresh_at_base(2) fresh_set insert_absorb list.set(2) ty_dom_inclusion)
  then show "False" using assms by auto
qed

lemma bound_removeAll_triple:
  fixes x xa :: vrs 
    and S T :: ty 
    and Ea :: "env" 
    and b ba::bool 
    and seen:: "vrs list"
  assumes "eqvt_at cv_sumC (Some S, Ea, b, seen)"
          "eqvt_at cv_sumC (Some Sa, Ea, b, seen)"
          "atom x \<sharp> (Ea, seen)" "atom xa \<sharp> (Ea, seen)"
          "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "removeAll x (cv_sumC (Some S, Ea, b, seen)) =
         removeAll xa (cv_sumC (Some Sa, Ea, b, seen))"
proof -
  from assms have 2: "[[atom x]]lst. S = [[atom xa]]lst. Sa"
    by(force simp add: Abs1_eq_iff'(3) fresh_Pair)
  have 3: "[[atom x]]lst. Ea = [[atom xa]]lst. Ea" 
      apply(rewrite Abs1_eq_iff_all(3)[of _ _ _ _ Ea]) 
      by (simp add: assms flip_fresh_fresh)
    have 4: "[[atom x]]lst. (Some S, Ea, b, seen) = [[atom xa]]lst. (Some Sa, Ea, b, seen)"
      using 2 3 
      apply(simp add: fresh_Pair fresh_Some permute_bool_def)
      by (metis assms(3) assms(4) flip_fresh_fresh fresh_PairD(2))
    have 5: "[[atom x]]lst. cv_sumC (Some S, Ea, b, seen) = 
             [[atom xa]]lst. cv_sumC (Some Sa, Ea, b, seen)"
      apply(rule Abs_lst1_fcb2'[OF 4(1), of _ "[]"])
         apply (simp add: Abs_fresh_iff(3))
        apply (simp add: fresh_star_list(3))
      using assms(1,2) unfolding eqvt_at_def by auto

    show "removeAll x (cv_sumC (Some S, Ea, b, seen)) =
          removeAll xa (cv_sumC (Some Sa, Ea, b, seen))" 
      using "5" bound_removeAll by blast
  qed

lemma bind_pair_commute:
  fixes x xa :: vrs and S T Sa Ta :: ty 
  assumes "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "[[atom x]]lst. (T, S) = [[atom xa]]lst. (Ta, Sa)"
  using assms apply(simp add: Abs1_eq_iff(3))
  by fastforce

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
  fixes x xa :: vrs and S Sa :: "ty option" and T :: vrs
  assumes "atom T \<sharp> x" "atom T \<sharp> xa"
  assumes "[[atom x]]lst. S = [[atom xa]]lst. Sa"
  shows "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, T)"
  using assms 
  apply(simp add: Abs1_eq_iff(3))
  apply safe
  by(simp_all add: flip_fresh_fresh fresh_Pair)

lemma bind_pair_proj_1:
  fixes x xa :: vrs and S T Sa Ta :: ty 
  assumes "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "[[atom x]]lst. S = [[atom xa]]lst. Sa"
  using assms
  by(auto simp add: Abs1_eq_iff(3) fresh_Pair)

lemma bind_pair_proj_2:
  fixes x xa :: vrs and S T Sa Ta :: ty 
  assumes "[[atom x]]lst. (S, T) = [[atom xa]]lst. (Sa, Ta)"
  shows "[[atom x]]lst. T = [[atom xa]]lst. Ta"
  using assms
  by(auto simp add: Abs1_eq_iff(3) fresh_Pair)

subsection \<open>Cv function\<close>



nominal_function cv :: "ty option \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> vrs list \<Rightarrow> vrs list"
where
  "cv (Some (Tvar x)) E b seen = 
    (if (b \<and> x \<notin> set seen \<and> length seen < length E) 
     then (case (extract_subtype x E) of
                 Some T \<Rightarrow> (cv (Some T) E True (x # seen))
                | None \<Rightarrow> []) 
     else [])"
| "cv (Some Top) E b seen = []"
| "atom x \<sharp> (E,seen) \<Longrightarrow> cv (Some (Arrow x S T)) E b seen = 
    (if b then removeAll x (cv (Some S) E False seen @ cv (Some T) E True seen) 
     else removeAll x (cv (Some S) E True seen @ cv (Some T) E False seen))"
| "atom X \<sharp> (E,seen) \<Longrightarrow> cv (Some (\<forall>X<:B. T)) E b seen = 
    (if b then (cv (Some B) E False seen @ (removeAll X (cv (Some T) E True seen))) 
     else (cv (Some B) E True seen @ (removeAll X (cv (Some T) E False seen))))"
| "cv (Some (C \<triangleright> T)) E b seen = 
    (if b then C @ cv (Some T) E True seen else cv (Some T) E False seen)"
| "cv None E b seen = []"
  using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal by(simp add: eqvt_def cv_graph_aux_def split: option.splits)
  subgoal premises prems for P x
  proof -
    obtain op E b where x_expr: "x = (op,E,b)" using prod_cases3 by blast 
    {fix t
      assume as: "op = Some t"
      obtain ba seen where b_expr: "b = (ba,seen)" by fastforce
      have "P"
        using prems
        apply(simp add: x_expr b_expr as)   
        apply(rule ty.strong_exhaust[of t P "(E,seen)"]) 
            apply(simp_all add: fresh_Pair)
        using fresh_star_insert fresh_PairD by blast+
    }
    note case1=this
    {assume as: "op = None"
    then have "P"
      using prems
      apply(simp add: x_expr)
      apply(cases "b")
      by blast
    }
    note case2=this
    show ?thesis
      using case1 case2 by blast
  qed
  subgoal for x E S T b seen xa Ea Sa Ta ba seena
    apply(safe, simp_all)
    using bind_pair_commute bound_removeAll_triple 
     apply smt
    using bind_pair_commute bound_removeAll_triple 
    by smt
  subgoal for X E seen B T b Xa Ea seena Ba Ta ba
    apply(safe; rule bound_removeAll_triple[of _ _ _ _ _ _ _ _ T Ta])
             apply blast+  
    by(auto simp add: Abs1_eq_iff(3) fresh_Pair)
  done

nominal_termination (eqvt)
  apply(relation "
         (\<lambda> (a,b,c,d). length b - length d) <*mlex*> 
         (\<lambda> (a,b,c,d). (case a of 
                       None \<Rightarrow> 0
                      | Some T \<Rightarrow> size T))  <*mlex*> {}", goal_cases) 
  apply(simp_all add: wf_mlex mlex_leq extract_subtype_if length_removeAll_less mlex_less)
  apply(simp add: mlex_iff)
  by auto

lemma or_inject: "a = b \<Longrightarrow> c = d \<Longrightarrow> (a \<or> c) = (b \<or> d)" by auto

nominal_function occurs_cov :: "ty \<Rightarrow> ty \<Rightarrow> bool \<Rightarrow> bool" where
  "occurs_cov Q (Tvar x) b = (b \<and> Q = Tvar x)"
| "occurs_cov Q Top b = (b \<and> Q = Top)"
| "atom x \<sharp> Q \<Longrightarrow> occurs_cov Q (Arrow x S T) b = 
   (occurs_cov Q S (\<not> b) \<or> occurs_cov Q T b)"
| "atom X \<sharp> Q \<Longrightarrow> occurs_cov Q (\<forall>X<:B. T) b = 
    (occurs_cov Q B (\<not> b) \<or> occurs_cov Q T b)"
| "occurs_cov Q (C \<triangleright> T) b = 
    (Q \<in> set (map Tvar C) \<or> occurs_cov Q T b)"
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

lemma cv_implies_1:
  shows "set C \<subseteq> set (cv (Some (C \<triangleright> T)) E True [])" by simp

lemma extract_append:
  assumes "extract_subtype x E = Some T"
          "\<turnstile> (E' @ E) ok"
  shows "extract_subtype x (E' @ E) = Some T"
  using assms
  apply(induction E')
  apply(simp_all split: option.splits, safe)
  using extract_fresh_none extract_subtype_b_iff by auto

lemma append_extract:
  assumes "\<turnstile> (E' @ E) ok"
          "extract_subtype x (E' @ E) = Some T"
          "(Tvar x) closed_in E"
  shows "extract_subtype x E = Some T"
  using assms
proof(induction E')
  case (Cons a E')
  from Cons(4) have "x \<in> set (ty_dom E)"
    unfolding closed_in_def
    apply(simp add: ty.supp supp_at_base)
    by fastforce
  then obtain Q where "TVarB x Q \<in> set E"
    using ty_dom_existence by blast
  then show ?case 
    using assms extract_append extract_subtype_if_some by fastforce
qed simp

lemma some_extract_imp_closed:
  "extract_subtype x E = Some T \<Longrightarrow> (Tvar x) closed_in E"  
  using closed_in_def empty_iff extract_subtype_if supp_at_base ty.supp(1) ty_dom_inclusion by fastforce


lemma extracted_imp_closed:
  "\<turnstile> E ok \<Longrightarrow> extract_subtype x E = Some T \<Longrightarrow> T closed_in E"
  using extract_subtype_if ok_closed(2) by blast

lemma 
  assumes "\<turnstile> (E' @ E) ok" "U closed_in E" 
  shows "cv (Some U) (E' @ E) b S = cv (Some U) E b S"
  using assms
proof(induction "(length E - length S, size U)" 
        arbitrary: U S b rule: less_induct)
  case less
  show ?case 
    apply(cases U rule: ty.strong_exhaust)
    subgoal for x1 
      apply(simp only: cv.simps split: if_splits option.splits)
      apply safe
            apply (simp add: extract_append less.prems(1))   
      apply simp
      using append_extract less.prems(1,2) apply auto[1]
      using append_extract less.prems(1,2) apply auto[1]
      subgoal premises prems for x2 x2a
      proof -
        thm less
        have "x2 = x2a"
          using extract_append less.prems(1) prems(2,3) by auto
        
        then show ?thesis
          using some_extract_imp_closed 
less(1)[of "x1 # S" x2a True, simplified] extracted_imp_closed
          apply simp
          
        
        thm less(1)[of "x1 # S" x2a True]
      qed
      thm extract_append
    sorry
qed


proof(nominal_induct "E' @ E" arbitrary: E' rule: valid_rel.strong_induct)
  case (valid_consT \<Gamma> X U)
  then show ?case sorry
next
  case (valid_cons \<Gamma> x T)
  then show ?case sorry
qed simp


lemma 
  assumes "\<turnstile> E ok" "TVarB x T \<in> set E"
  shows "cv (Some T) E True [x] = cv (Some T) E True []"
  using assms
proof(nominal_induct E arbitrary: x T rule: valid_rel.strong_induct)
  case (valid_consT \<Gamma> X U)
  then show ?case 
    apply simp
    apply safe
    
    sorry
next
  case (valid_cons \<Gamma> x T)
  then show ?case sorry
qed simp

lemma cv_implies_2:
  assumes "\<turnstile> E ok" "TVarB x T \<in> set E"
  shows "TVarB x T \<in> set E \<Longrightarrow> 
          (cv (Some (Tvar x)) E True [] = cv (Some T) E True [x])"
  using assms
  apply(simp only: cv.simps split: if_splits option.splits)
  using extract_subtype_iff[OF assms(1), of x T] by auto

lemma cv_implies_3:
  assumes "occurs_cov S T True"
  shows "set (cv (Some S) E True []) \<subseteq> 
          set (cv (Some T) E True [])"
  using assms
proof(nominal_induct T avoiding: S E rule: ty.strong_induct)
  case (Tvar x)
  then show ?case by(simp only: occurs_cov.simps)
next
  case Top
  then show ?case by(simp only: occurs_cov.simps)
next
  case (Arrow x1a x2 x3)
  then show ?case 
    apply(simp add: fresh_Nil Arrow(2))
    thm Arrow(4)[of S E]
    apply safe
   
    thm fresh_Nil
    thm cv.simps(3)
    sorry
next
  case (Forall x1a x2 x3)
  then show ?case sorry
next
  case (CapSet x1a x2)
  then show ?case sorry
qed



proof(induction S T "True" rule: occurs_cov.induct)
  case (1 Q x)
  then show ?case by(simp only: occurs_cov.simps)
next
  case (2 Q)
  then show ?case by(simp only: occurs_cov.simps)
next
  case (3 x Q S T)
  then show ?case 
    apply(simp only: occurs_cov.simps)
   
    sorry
next
  case (4 X Q B T)
  then show ?case sorry
next
  case (5 Q C T)
  then show ?case sorry
qed



definition cv_vrs :: "vrs \<Rightarrow> env \<Rightarrow> vrs list" where
  "cv_vrs x E = (case (extract_types x E) of
                 Some T \<Rightarrow> (cv (Some T) (removeAll (VarB x T) E) True [])
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
| "atom X\<sharp>(y,C) \<Longrightarrow> (\<forall>X<:B. T\<^sub>1)[y \<mapsto> C]\<^sub>c = (\<forall>X<:B. T\<^sub>1[y \<mapsto> C]\<^sub>c)"
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
  SA_refl[intro]:      "\<Gamma> \<turnstile> T <: T"
| SA_trans[intro]:     "\<lbrakk>\<Gamma> \<turnstile> R <: S; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> R <: T"
| SA_TVar[intro]:      "\<lbrakk>ListMem X (ty_dom \<Gamma>); extract_subtype X \<Gamma> = Some T\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Tvar X <: T"
| SA_Top[intro]:       " cv (Some T) E True [] = [] \<Longrightarrow> \<Gamma> \<turnstile> T <: Top"
| SA_arrow[intro]:     "\<lbrakk>\<Gamma> \<turnstile> S\<^sub>2 <: S\<^sub>1; ((VarB x S\<^sub>2) # \<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>2\<rbrakk> \<Longrightarrow> 
                         \<Gamma> \<turnstile> (Arrow x S\<^sub>1 T\<^sub>1) <: (Arrow x S\<^sub>2 T\<^sub>2)" 
| SA_all[intro]:       "\<lbrakk>\<Gamma> \<turnstile> S\<^sub>2 <: S\<^sub>1; ((VarB x S\<^sub>2) # \<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>2\<rbrakk> \<Longrightarrow> 
                        \<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. T\<^sub>1) <: (\<forall>X<:S\<^sub>2. T\<^sub>2)"
| SA_captr[intro]:     "\<Gamma> \<turnstile> T <: (C \<triangleright> T)"
| SA_capti[intro]:     "\<lbrakk>\<Gamma> \<turnstile> S <: T; set C \<subseteq> set (cv (Some T) E True [])\<rbrakk> \<Longrightarrow> 
                         \<Gamma> \<turnstile> (C \<triangleright> S) <: T"

equivariance subtype_of

nominal_inductive subtype_of done

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
| T_App[intro]: "\<lbrakk> \<Gamma> \<turnstile> t : (C \<triangleright> Arrow x R T); 
                   \<Gamma> \<turnstile> s : S;
                   \<Gamma> \<turnstile> S <: R[x \<mapsto> (cv (Some S) \<Gamma> True [])]\<^sub>c \<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> t \<cdot> s : T[x \<mapsto> (cv (Some S) \<Gamma> True [])]\<^sub>c"
| T_TApp[intro]:"\<lbrakk> atom X \<sharp> (\<Gamma>,t,S);
                   \<Gamma> \<turnstile> t : (C \<triangleright> (Forall X T R)); 
                   \<Gamma>; [] \<turnstile> S wf;
                   \<Gamma> \<turnstile> S <: R[x \<mapsto> (cv (Some S) \<Gamma> True [])]\<^sub>c\<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> t \<cdot>\<^sub>\<tau> S : ((T[X \<mapsto> S]\<^sub>\<tau>)[x \<mapsto> (cv (Some S) \<Gamma> True [])]\<^sub>c)" 
| T_Abs[intro]: "\<lbrakk> VarB x S # \<Gamma> \<turnstile> t : T;
                   \<Gamma> ; [VarB x S] \<turnstile> S wf \<rbrakk> \<Longrightarrow> 
                  \<Gamma> \<turnstile> (Abs x t T) : 
                      ((removeAllList (cv_trm t E) 
                                     (cv (Some T) E True [])) \<triangleright> 
                        (Arrow x S T))"
| T_TAbs[intro]: "\<lbrakk> TVarB X S # \<Gamma> \<turnstile> t : T;
                   \<Gamma> ; [TVarB X S] \<turnstile> S wf \<rbrakk> \<Longrightarrow> 
                  \<Gamma> \<turnstile> (TAbs X t T) : 
                      ((removeAllList (cv_trm t E) 
                                     (cv (Some T) E True [])) \<triangleright> 
                        (Arrow X S T))"

equivariance typing
nominal_inductive typing done 

lemma typing_ok:
  assumes "\<Gamma> \<turnstile> t : T"
  shows   "\<turnstile> \<Gamma> ok"
  using assms 
  apply (induct) 
  using valid_rel.cases by auto

section \<open>Substitution lemma\<close>
(*
lemma 
  shows "set (cv_trm (t[Y \<mapsto>\<^sub>\<tau> T]) E) =
         set (cap_subst (cv_trm t E) Y (cv (Some T) E True))" 
proof(rule trm.strong_exhaust[of t], goal_cases)
  case (1 x1)
  then have "set (cv_trm (t[Y \<mapsto>\<^sub>\<tau> T]) E) = 
             set (cv_vrs x1 E)"
    unfolding cv_trm_def by auto
  from 1 have "set (cap_subst (cv_trm t E) Y (cv (Some T) E True)) =
               set (cap_subst (cv_vrs x1 E) Y (cv (Some T) E True))"
    unfolding cv_trm_def by auto
  have "set (cv_vrs x1 E) =
        set (cap_subst (cv_vrs x1 E) Y (cv (Some T) E True))"
    unfolding cv_vrs_def
    apply(simp_all split: if_splits option.splits; safe)
    apply (simp add: cap_subst_nil) 

  then show ?case
    unfolding cv_trm_def cv_vrs_def
  apply(simp_all split: if_splits option.splits; safe)
      apply (simp add: cap_subst_nil) 
    unfolding cap_subst_def
     apply(simp_all split: if_splits option.splits; safe)
    defer 1
   
     apply safe
     defer 1
    apply simp
    sorry
    
 
  
  assume 1: "Y \<in> set (cv_trm t E)"
  show "cv_trm (t[Y \<mapsto>\<^sub>\<tau> T]) E =
        removeAll Y (cv_trm t E) @ cv (Some T) E True"
    apply(rule trm.strong_exhaust[of t])
    apply simp
    unfolding cv_trm_def
        apply simp
    unfolding cv_vrs_def
            apply(simp split: option.splits)
            apply safe
        apply force
        
        
    
  sorry
*)
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

section \<open>Characterization of cv\<close>


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

lemma in_capset_triple:
  fixes xa S Sa :: "vrs" and T Ta y ya :: "ty"
  assumes "eqvt_at in_capset_sumC (Some T, xa)"
          "eqvt_at in_capset_sumC (Some y, xa)"
          "eqvt_at in_capset_sumC (Some Ta, xa)"
          "eqvt_at in_capset_sumC (Some ya, xa)"
          "atom xa \<sharp> S"
          "atom xa \<sharp> Sa"
          "[[atom S]]lst. (T, y) = [[atom Sa]]lst. (Ta, ya) \<and> x = xa"
  shows "(in_capset_sumC (Some T, xa) \<or> in_capset_sumC (Some y, xa)) =
        (in_capset_sumC (Some Ta, xa) \<or> in_capset_sumC (Some ya, xa))"
proof -
  from assms have 2: "[[atom S]]lst. T = [[atom Sa]]lst. Ta"
    by(force simp add: Abs1_eq_iff'(3) fresh_Pair)
  from assms have 3: "[[atom S]]lst. y = [[atom Sa]]lst. ya" 
    by(force simp add: Abs1_eq_iff'(3) fresh_Pair)
  have 4: "[[atom S]]lst. (Some T, xa) = [[atom Sa]]lst. (Some Ta, xa)"
          "[[atom S]]lst. (Some y, xa) = [[atom Sa]]lst. (Some ya, xa)"
    using 2 3 
    apply(simp_all add: fresh_Pair fresh_Some permute_bool_def)
    using assms by force+
  have 4: "[[atom S]]lst. in_capset_sumC (Some T, xa) = 
           [[atom Sa]]lst. in_capset_sumC (Some Ta, xa)"
          "[[atom S]]lst. in_capset_sumC (Some y, xa) = 
           [[atom Sa]]lst. in_capset_sumC (Some ya, xa)"
     apply(rule Abs_lst1_fcb2'[OF 4(1), of _ "[]"])
         apply (simp add: Abs_fresh_iff(3))
        apply (simp add: fresh_star_list(3))
    using assms(1,3) unfolding eqvt_at_def apply force
    using assms(1,3) unfolding eqvt_at_def apply force
    apply(rule Abs_lst1_fcb2'[OF 4(2), of _ "[]"])
         apply (simp add: Abs_fresh_iff(3))
        apply (simp add: fresh_star_list(3))
    using assms(2,4) unfolding eqvt_at_def apply force
    using assms(2,4) unfolding eqvt_at_def by force

  have 5: "[[atom S]]lst. (in_capset_sumC (Some T, xa) \<or>
                           in_capset_sumC (Some y, xa)) = 
           [[atom Sa]]lst. (in_capset_sumC (Some Ta, xa) \<or>
                           in_capset_sumC (Some ya, xa))"  
    by (smt "4"(1) "4"(2) Abs1_eq_iff'(3) False_eqvt)

  show ?thesis 
    apply(rule Abs_lst1_fcb2'[of S _ Sa _ _ "[]"])
    using 5 apply blast
       apply (simp add: pure_fresh)
      apply (simp add: fresh_star_list(3))
    by blast+
qed

nominal_function in_capset :: "ty option \<Rightarrow> vrs \<Rightarrow> bool" where
  "in_capset (Some (Tvar x)) y = False"
| "in_capset (Some Top) y = False"
| "atom y \<sharp> x \<Longrightarrow> in_capset (Some (Arrow x S T)) y = 
    ((in_capset (Some S) y) \<or> (in_capset (Some T) y))"
| "atom y \<sharp> X \<Longrightarrow> in_capset (Some (\<forall>X<:B. T)) y = 
    ((in_capset (Some B) y) \<or> (in_capset (Some T) y))"
| "in_capset (Some (C \<triangleright> T)) y = 
    ((y \<in> set C) \<or> (in_capset (Some T) y))"
| "in_capset None y = False"
  using [[simproc del: alpha_lst]]  
  apply(simp_all split: option.splits)
  subgoal by(simp add: eqvt_def in_capset_graph_aux_def split: option.splits)  
  subgoal premises prems for P x
  proof -
    obtain op v where x_expr: "x = (op,v)" using prod_cases by force
    { fix t
      assume as: "op = Some t"
      have "P"
        using prems
        apply(simp add: x_expr as) 
        apply(rule ty.strong_exhaust[of t P "v"]) 
            apply blast+
        using fresh_at_base(2) fresh_star_insert by fastforce+
    }
    note case1=this
    {
      assume as: "op = None"
      then have "P"
        using prems
        by(simp add: x_expr)
    }
    note case2=this
    show ?thesis
      using case1 case2 by blast
  qed
  subgoal for y x S T ya xa Sa Ta
    using in_capset_triple by blast
  subgoal premises prems for y X B T ya Xa Ba Ta
  proof(rule Abs_lst1_fcb2'[of X _ Xa _ _ "[]"], goal_cases)
    case 1
    have 2: "[[atom X]]lst. (Some T, ya) =
             [[atom Xa]]lst. (Some Ta, ya)"
      apply(rule bind_pair_add_vrs)
      using prems apply simp+
      using prems(6) binding_some by blast

    show ?case
      apply(rule binding_or)
       apply (simp add: Abs1_eq_iff'(3) permute_bool_def pure_fresh)
      apply(rule Abs_lst1_fcb2'[OF 2, of _ "[]"])
         apply (simp add: Abs_fresh_iff(3))
        apply (simp add: fresh_star_list(3))
      using prems(1,3) unfolding eqvt_at_def apply force
      using prems(1,3) unfolding eqvt_at_def by force
  qed (simp add: pure_fresh fresh_star_list(3); blast)+
  done

nominal_termination (eqvt)
  by lexicographic_order

lemma partial_characterization:
  assumes "x \<in> set (cv T E b S)"
  shows "in_capset T x \<or> 
         (\<exists> X B L b'. TVarB X B \<in> set E \<and> x \<in> set (cv (Some B) E b' L))"
  using assms
proof(cases "T")
  case None
  then show ?thesis using assms by fastforce
next
  case (Some a)
  then show ?thesis 
    using assms
  proof(nominal_induct a avoiding: x E S arbitrary: T b rule: ty.strong_induct)
    case (Tvar x)
    then show ?case 
      apply(simp only: cv.simps in_capset.simps split: if_splits option.splits)
        apply force
       apply simp
       using extract_subtype_if apply blast
       by auto
  next
    case Top
    then show ?case by auto
  next
    case (Arrow x1a x2 x3)
    then show ?case 
      apply(simp only: cv.simps in_capset.simps split: if_splits option.splits)
      apply(simp)
      apply safe
      apply(cases "b")
       apply simp_all
      apply safe
      by meson+
  next
    case (Forall x1a x2 x3)
    then show ?case 
      apply(simp only: cv.simps in_capset.simps split: if_splits option.splits)
      apply simp
      apply safe
      apply(cases "b")
       apply simp_all
      apply safe
      by meson+
  next
    case (CapSet x1a x2)
    then show ?case  
      apply(simp only: cv.simps in_capset.simps split: if_splits option.splits)
       apply fastforce
      by fast
  qed
qed

(*nominal_function in_contra_capset :: "ty option \<Rightarrow> vrs \<Rightarrow> bool" where
  "in_capset (Some (Tvar x)) y = False"
| "in_capset (Some Top) y = False"
| "atom y \<sharp> x \<Longrightarrow> in_capset (Some (Arrow x S T)) y = 
    ((in_capset (Some S) y) \<or> (in_capset (Some T) y))"
| "atom y \<sharp> X \<Longrightarrow> in_capset (Some (\<forall>X<:B. T)) y = 
    ((in_capset (Some B) y) \<or> (in_capset (Some T) y))"
| "in_capset (Some (C \<triangleright> T)) y = 
    ((y \<in> set C) \<or> (in_capset (Some T) y))"
| "in_capset None y = False*)




lemma 
  assumes "\<turnstile> (E' @ E) ok" "set S \<subseteq> set (ty_dom E)"
  shows "set (cv T E b S) \<subseteq> set (cv T (E' @ E) b S)"
  using assms
proof(nominal_induct "E' @ E" arbitrary: E' rule: valid_rel.strong_induct)
  case (valid_consT \<Gamma> X U)
  show ?case 
  proof 
    fix x
    assume "x \<in> set (cv T E b S)"
    then have "in_capset T x \<or> 
         (\<exists> X B L b'. TVarB X B \<in> set E \<and> x \<in> set (cv (Some B) E b' L))"
      using partial_characterization by blast
    then show ?thesis
  
  qed
    sorry
next
  case (valid_cons \<Gamma> x T)
  then show ?case sorry
qed simp

section \<open>Term subtyping lemma\<close>

lemma type_weaken:
  assumes "(\<Delta>@\<Gamma>) \<turnstile> t : T"
  and     "\<turnstile> (\<Delta> @ B # \<Gamma>) ok"
  shows   "(\<Delta> @ B # \<Gamma>) \<turnstile> t : T"
  using assms
proof(nominal_induct "\<Delta> @ \<Gamma>" t T avoiding: \<Delta> \<Gamma> B rule: typing.strong_induct)
  case (T_Var x T)
  then show ?case by auto
next
  case (T_App t C x R T s S)
  then show ?case     
    apply(rule typing.T_App)
    thm typing.T_App
    sorry
next
  case (T_TApp X t S C T R x)
  then show ?case sorry
next
  case (T_Abs x S t T E)
  then show ?case sorry
next
  case (T_TAbs X S t T E)
  then show ?case sorry
qed

lemma type_weaken':
 "\<Gamma> \<turnstile> t : T \<Longrightarrow>  \<turnstile> (\<Delta>@\<Gamma>) ok \<Longrightarrow> (\<Delta>@\<Gamma>) \<turnstile> t : T"
  apply (induct \<Delta>)
  apply simp_all
  apply (erule validE)
  apply (insert type_weaken [of "[]", simplified])
  apply simp_all
  done

theorem subst_type: 
  assumes H: "(\<Delta> @ (VarB x U) # \<Gamma>) \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> u : U \<Longrightarrow> 
         \<Delta> @ \<Gamma> \<turnstile> t[x \<mapsto> u] : T[x \<mapsto> cv (Some U) (\<Delta> @ \<Gamma>) True]\<^sub>c" using H
proof (nominal_induct "\<Delta> @ (VarB x U) # \<Gamma>" t T avoiding: x u arbitrary: \<Delta> rule: typing.strong_induct)
  case (T_Var y T)
  then show ?case 
   proof (cases "x = y")
   assume eq:"x=y"
   then have "T=U" using T_Var uniqueness_of_ctxt' 
     by (meson in_set_conv_decomp)
   then show ?case using eq T_Var
     apply simp
     by (auto intro: type_weaken' dest: valid_cons')
 next
   assume "x\<noteq>y"
   then show ?case using T_Var
     apply simp
     thm typing.T_Var
     by (auto simp add:binding.inject dest: valid_cons')
 qed  
    sorry
next
  case (T_App t C x R T s S)
  then show ?case sorry
next
  case (T_Sub t S T)
  then show ?case sorry
next
  case (T_TApp X t S C T R x)
  then show ?case sorry
next
  case (T_Abs x S t T E)
  then show ?case sorry
next
  case (T_TAbs X S t T E)
  then show ?case sorry
qed

lemma Abs_type: \<comment> \<open>A.13(1)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda>x:S. s) : T"
  and H': "\<Gamma> \<turnstile> T <: U \<rightarrow> U'"
  and H'': "x \<sharp> \<Gamma>"
  obtains S' where "\<Gamma> \<turnstile> U <: S"
             and   "(VarB x S) # \<Gamma> \<turnstile> s : S'"
             and   "\<Gamma> \<turnstile> S' <: U'"
  using H H' H''
proof (nominal_induct \<Gamma> t \<equiv> "\<lambda>x:S. s" T avoiding: x arbitrary: U U' S s rule: typing.strong_induct)
  case (T_Abs y T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> T\<^sub>1 \<rightarrow> T\<^sub>2 <: U \<rightarrow> U'\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: S" and ty2: "\<Gamma> \<turnstile> T\<^sub>2 <: U'" using T_Abs
    by cases (simp_all add: ty.inject trm.inject alpha fresh_atm)
  from T_Abs have "VarB y S # \<Gamma> \<turnstile> [(y, x)] \<bullet> s : T\<^sub>2"
    by (simp add: trm.inject alpha fresh_atm)
  then have "[(y, x)] \<bullet> (VarB y S # \<Gamma>) \<turnstile> [(y, x)] \<bullet> [(y, x)] \<bullet> s : [(y, x)] \<bullet> T\<^sub>2"
    by (rule typing.eqvt)
  moreover from T_Abs have "y \<sharp> \<Gamma>"
    by (auto dest!: typing_ok simp add: fresh_trm_dom)
  ultimately have "VarB x S # \<Gamma> \<turnstile> s : T\<^sub>2" using T_Abs
    by (perm_simp add: ty_vrs_prm_simp)
  with ty1 show ?case using ty2 by (rule T_Abs)
next
  case (T_Sub \<Gamma> t S T)
  then show ?case using subtype_transitivity by blast
qed simp_all

section \<open>Soundness\<close>

theorem preservation: 
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t \<longmapsto> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : T" using H
proof (nominal_induct avoiding: t' rule: typing.strong_induct)
  case (T_Var x T \<Gamma>)
  then show ?case using eval.cases by force
next
  case (T_App \<Gamma> t C x R T s S t')
  then show ?case 
  proof -
    from \<open>t \<cdot> s \<longmapsto> t'\<close> show ?case
    proof(cases rule: eval.cases)
      case (E_Abs y q Q) 
      have "\<Gamma> \<turnstile> (\<lambda>y:Q. q): (C \<triangleright> (Arrow x R T))"
        using E_Abs T_App by auto
      then obtain Q' where "\<Gamma> \<turnstile> q: Q'" "\<Gamma> \<turnstile> Q' <: T"
        apply(nominal_induct \<Gamma> "(\<lambda>y:Q. q)" "(C \<triangleright> (Arrow x R T))"
              rule: typing.strong_induct)
        
      thm typing.T_Abs
      have "atom y \<sharp> \<Gamma>"
        oops
      thm T_App
      show ?thesis 
        apply(simp add: E_Abs)
      sorry
    next
      case (E_App1 q)
      then show ?thesis sorry
    next
      case (E_App2 v q q')
      then have 0: "t = v" "s = q"
        by(simp add: trm.inject)+
      then have 1: "\<Gamma> \<turnstile> q : ( C\<^sub>2 \<triangleright> S)" 
        using T_App E_App1 by blast
      show ?thesis 
        apply(simp add: E_App2)
        apply(rule typing.T_App)
        using T_App(2) 0 apply blast
        using 0 T_App.hyps(5) local.E_App2(4) apply blast
        using T_App apply meson
        apply(simp add: fresh_prod, safe)
        using T_App E_App2 by auto
    qed (simp_all add: fresh_prod)
next
  case (T_Sub \<Gamma> t S T)
  then show ?case by blast
next
  case (T_TApp X \<Gamma> t S C T R x)
  then show ?case sorry
next
  case (T_Abs x S \<Gamma> t T E)
  then show ?case using eval.cases by fastforce
next
  case (T_TAbs X S \<Gamma> t T E)
  then show ?case using eval.cases by fastforce
qed

end
