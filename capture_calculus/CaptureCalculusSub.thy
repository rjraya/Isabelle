theory CaptureCalculusSub
  imports "HOL-Nominal.Nominal" 
          "HOL-Library.Rewrite"
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
  | CapAbs "\<guillemotleft>vrs\<guillemotright>aty"
  | Forall "\<guillemotleft>vrs\<guillemotright>ty" "ty" 
  | CapSet "vrs list" "ty"
and aty =
    Arrow  "ty" "ty"         (infixr "\<rightarrow>" 200)


nominal_datatype trm = 
    Var   "vrs"
  | Abs   "\<guillemotleft>vrs\<guillemotright>ltrm" 
  | TAbs  "\<guillemotleft>vrs\<guillemotright>trm" "ty"
  | App   "trm" "trm" (infixl "\<cdot>" 200)
  | TApp  "trm" "ty"  (infixl "\<cdot>\<^sub>\<tau>" 200)
and ltrm =
   Lambda trm ty

text \<open>To be polite to the eye, some more familiar notation is introduced. 
  Because of the change in the order of arguments, one needs to use 
  translation rules, instead of syntax annotations at the term-constructors
  as given above for \<^term>\<open>Arrow\<close>.\<close>

abbreviation
  Forall_syn :: "vrs \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"  ("(3\<forall>_<:_./ _)" [0, 0, 10] 10) 
where
  "\<forall>X<:T\<^sub>1. T\<^sub>2 \<equiv> ty.Forall X T\<^sub>2 T\<^sub>1"

abbreviation
  Abs_syn    :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"  ("(3\<lambda>_:_./ _)" [0, 0, 10] 10) 
where
  "\<lambda>x:T. t \<equiv> trm.Abs x (Lambda t T)"

abbreviation
  TAbs_syn   :: "vrs \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("(3\<lambda>_<:_./ _)" [0, 0, 10] 10) 
where
  "\<lambda>X<:T. t \<equiv> trm.TAbs X t T"

abbreviation
  CapSet_syn   :: "vrs list \<Rightarrow> ty \<Rightarrow> ty" ("(2_ \<triangleright> _)" [0, 10] 10) 
where
  "C \<triangleright> T \<equiv> ty.CapSet C T"

subsection \<open>Environment\<close>

nominal_datatype binding = 
    VarB vrs ty 
  | TVarB vrs ty

type_synonym env = "binding list"

text \<open>In order to state validity-conditions for typing-contexts, the notion of
  a \<open>dom\<close> of a typing-context is handy.\<close>

nominal_primrec "tyvrs_of" :: "binding \<Rightarrow> vrs set"
where
  "tyvrs_of (VarB  x y) = {}"
| "tyvrs_of (TVarB x y) = {x}"
  by auto

nominal_primrec "vrs_of" :: "binding \<Rightarrow> vrs set"
where
  "vrs_of (VarB  x y) = {x}"
| "vrs_of (TVarB x y) = {}"
by auto

primrec "ty_dom" :: "env \<Rightarrow> vrs set"
where
  "ty_dom [] = {}"
| "ty_dom (X#\<Gamma>) = (tyvrs_of X)\<union>(ty_dom \<Gamma>)" 

primrec "trm_dom" :: "env \<Rightarrow> vrs set"
where
  "trm_dom [] = {}"
| "trm_dom (X#\<Gamma>) = (vrs_of X)\<union>(trm_dom \<Gamma>)" 

subsection \<open>Auxiliary functions\<close>

lemma removeAll_eqvt[eqvt]:
  fixes y::"vrs"
  shows "(pi::vrs prm)\<bullet>(removeAll y C) = removeAll (pi\<bullet>y) (pi\<bullet>C)"
  apply(induction C)
  by(induction C, auto simp add: perm_bij)

lemma fresh_removeAll:
  "(x::vrs) \<sharp> removeAll x list" 
  apply(induction list)
  by(auto simp add: fresh_list_nil fresh_atm fresh_list_cons)

nominal_primrec
  fv :: "trm \<Rightarrow> vrs list"
  and lfv :: "ltrm \<Rightarrow> vrs list"
where
  "fv (Var x) = [x]"
| "fv (Abs x lamb) = removeAll x (lfv lamb)"
| "X \<sharp> T  \<Longrightarrow> fv (\<lambda>X<:T. t) = removeAll X (fv t)"
| "fv (t \<cdot> s) = fv t @ fv s"
| "fv (t \<cdot>\<^sub>\<tau> T) = fv t"
| "lfv (Lambda t T) = fv t"
  apply (simp_all)
  apply (finite_guess)+
  using fresh_removeAll apply simp+ 
  by (fresh_guess add: fresh_removeAll)+  

lemma fv_eqvt[eqvt]:
  fixes pi::"vrs prm" and t::"trm" and lt::"ltrm"
  shows "pi\<bullet>(fv t) = fv (pi\<bullet>t)"
        "pi\<bullet>(lfv lt) = lfv (pi\<bullet>lt)"
  by(nominal_induct t and lt rule: trm_ltrm.strong_inducts)
     (auto simp add: fresh_bij eqvts)

nominal_primrec extract_subtype_b :: "vrs \<Rightarrow> binding \<Rightarrow> ty option" where
  "extract_subtype_b x (VarB y T) = None"
| "extract_subtype_b x (TVarB y T) = (if x = y then Some T else None)"
  by auto

primrec extract_subtype :: "vrs \<Rightarrow> env \<Rightarrow> ty option" where
  "extract_subtype x [] = (None::ty option)"
| "extract_subtype x (b # bs) = 
    (case (extract_subtype_b x b) of
      None \<Rightarrow> None
    | Some T \<Rightarrow> Some T)
    "

(*
cv(x, E)             = cv(T, E)                     if x <: T in E
cv((x: S) -> T, E)   = dv(S, E) u cv(T, E) \ {x}
cv([x <: S] -> T, E) = dv(S, E) u cv(T, E) \ {x}
cv(C |> T, E)        = C u cv(T, E)
cv(Top, E)           = {}

dv(x, E)             = {}
dv((x: S) -> T, E)   = cv(S, E) u dv(T, E) \ {x}
dv([x <: S] -> T, E) = cv(S, E) u dv(T, E) \ {x}
dv(C |> T, E)        = dv(T, E)
dv(Top, E)           = {}
*)
nominal_primrec
  cv :: "ty \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> vrs list"
  and acv :: "aty \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> vrs list"
where
  "cv (Tvar x) E b = 
    (if b then (case (extract_subtype x E) of
                    None \<Rightarrow> []
                  | Some T \<Rightarrow> cv T E True) else [])"
| "cv Top E b = []"
| "cv (CapAbs x A) E b = 
    (if b then removeAll x (acv A E True) else removeAll x (acv A E False))"
| "cv (\<forall>X<:B. T) E b = 
    (if b then removeAll X (cv B E False @ cv T E True) 
     else removeAll X (cv B E True @ cv T E False))"
| "cv (C \<triangleright> T) E b = 
    (if b then C @ cv T E True else cv T E False)"
| "acv (Arrow S T) E b = 
    (if b then (cv T E True @ cv T E True)
     else (cv T E True @ cv T E True))"
(*
| 


*)

  apply (simp_all)
  apply (finite_guess)+
  using fresh_removeAll apply simp+ 
  by (fresh_guess add: fresh_removeAll)+  



section \<open>Substitution\<close>

nominal_primrec
   subst_trm :: "trm \<Rightarrow> vrs \<Rightarrow> trm \<Rightarrow> trm"  ("_[_ \<mapsto> _]" [300, 0, 0] 300)
  and subst_ltrm :: "ltrm \<Rightarrow> vrs \<Rightarrow> trm \<Rightarrow> ltrm"
where
  "(Var x)[y \<mapsto> t] = (if x=y then t else (Var x))"
| "x\<sharp>(y,t) \<Longrightarrow> (Abs x lamb)[y \<mapsto> t] = (Abs x (subst_ltrm lamb y t))"
| "X\<sharp>(t,T,y) \<Longrightarrow> (\<lambda>X<:T. t\<^sub>1)[y \<mapsto> t] = (\<lambda>X<: T. t\<^sub>1[y \<mapsto> t])" 
| "(t1 \<cdot> t2)[y \<mapsto> t] = (t1[y \<mapsto> t]) \<cdot> (t2[y \<mapsto> t])"
| "(t\<^sub>1 \<cdot>\<^sub>\<tau> T)[y \<mapsto> t] = ((t\<^sub>1[y \<mapsto> t]) \<cdot>\<^sub>\<tau> T)"
| "subst_ltrm (Lambda t\<^sub>1 T) y t = Lambda (t\<^sub>1[y \<mapsto> t]) T"
  apply(finite_guess)+
  apply(rule TrueI)+
  apply(simp add: abs_fresh)+
  apply(fresh_guess add: abs_fresh)+
  done

lemma subst_trm_eqvt[eqvt]:
  fixes pi::"vrs prm" and t::"trm" and lt::"ltrm"
  shows "pi\<bullet>(t[x \<mapsto> u]) = (pi\<bullet>t)[(pi\<bullet>x) \<mapsto> (pi\<bullet>u)]"
        "pi\<bullet>(subst_ltrm lt x u) = subst_ltrm (pi\<bullet>lt) (pi\<bullet>x) (pi\<bullet>u)"
  by(nominal_induct t and lt  avoiding: x u rule: trm_ltrm.strong_inducts)
    (perm_simp add: fresh_left)+

nominal_primrec
  subst_ty :: "ty \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> ty" ("_[_ \<mapsto> _]\<^sub>\<tau>" [300, 0, 0] 300)
  and subst_aty :: "aty \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> aty"
where
  "(Tvar X)[Y \<mapsto> T]\<^sub>\<tau> = (if X=Y then T else Tvar X)" 
| "Top[Y \<mapsto> T]\<^sub>\<tau> = Top"
| "x\<sharp>(Y,T) \<Longrightarrow> (CapAbs x A)[Y \<mapsto> T]\<^sub>\<tau> = (CapAbs x (subst_aty A Y T))"
| "X\<sharp>(Y,T,B) \<Longrightarrow> (\<forall>X<:B. T\<^sub>1)[Y \<mapsto> T]\<^sub>\<tau> = (\<forall>X<:B[Y \<mapsto> T]\<^sub>\<tau>. T\<^sub>1[Y \<mapsto> T]\<^sub>\<tau>)"
| "(x \<triangleright> T\<^sub>1)[Y \<mapsto> T]\<^sub>\<tau> = (x \<triangleright> T\<^sub>1[Y \<mapsto> T]\<^sub>\<tau>)"
| "subst_aty (S\<^sub>1 \<rightarrow> S\<^sub>2) Y T = (S\<^sub>1[Y \<mapsto> T]\<^sub>\<tau> \<rightarrow> S\<^sub>2[Y \<mapsto> T]\<^sub>\<tau>)"
  apply (finite_guess)+
  apply (rule TrueI)+
  apply (simp add: abs_fresh)+ 
  by(fresh_guess)+  

lemma subst_eqvt[eqvt]:
  fixes pi::"vrs prm" and T::"ty" and aT::"aty"
  shows "pi\<bullet>(T[X \<mapsto> T']\<^sub>\<tau>) = (pi\<bullet>T)[(pi\<bullet>X) \<mapsto> (pi\<bullet>T')]\<^sub>\<tau>"
        "pi\<bullet>(subst_aty aT X T') = subst_aty (pi\<bullet>aT) (pi\<bullet>X) (pi\<bullet>T')"
  by(nominal_induct T and aT avoiding: X T' rule: ty_aty.strong_inducts)
    (perm_simp add: fresh_bij)+

lemma type_subst_fresh':
  fixes X::"vrs" and T :: ty and aT :: aty
  assumes "X\<sharp>T" and "X\<sharp>aT" and "X\<sharp>P"
  shows   "X\<sharp>T[Y \<mapsto> P]\<^sub>\<tau>" and "X\<sharp>subst_aty aT Y P"
  using assms 
  apply(nominal_induct T and aT avoiding: X Y P 
        arbitrary: aT and T rule: ty_aty.strong_inducts)
  apply(simp_all add: abs_fresh) 
  apply force 
  using aty.fresh by blast+

lemma type_subst_fresh:
  fixes X::"vrs" and T :: ty 
  assumes "X\<sharp>T" and "X\<sharp>P"
  shows   "X\<sharp>T[Y \<mapsto> P]\<^sub>\<tau>" 
  using type_subst_fresh' assms aty.fresh by meson

nominal_primrec (freshness_context: "T2::ty")
  subst_trm_ty :: "trm \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> trm"  ("_[_ \<mapsto>\<^sub>\<tau> _]" [300, 0, 0] 300)
  and subst_ltrm_ty :: "ltrm \<Rightarrow> vrs \<Rightarrow> ty \<Rightarrow> ltrm"
where
  "(Var x)[Y \<mapsto>\<^sub>\<tau> T2] = Var x"
| "(t1 \<cdot> t2)[Y \<mapsto>\<^sub>\<tau> T2] = t1[Y \<mapsto>\<^sub>\<tau> T2] \<cdot> t2[Y \<mapsto>\<^sub>\<tau> T2]"
| "(t1 \<cdot>\<^sub>\<tau> T)[Y \<mapsto>\<^sub>\<tau> T2] = t1[Y \<mapsto>\<^sub>\<tau> T2] \<cdot>\<^sub>\<tau> T[Y \<mapsto> T2]\<^sub>\<tau>"
| "X\<sharp>(Y,T,T2) \<Longrightarrow> (\<lambda>X<:T. t)[Y \<mapsto>\<^sub>\<tau> T2] = (\<lambda>X<:T[Y \<mapsto> T2]\<^sub>\<tau>. t[Y \<mapsto>\<^sub>\<tau> T2])" 
| "x\<sharp>(Y,T2) \<Longrightarrow> (Abs x lamb)[Y \<mapsto>\<^sub>\<tau> T2] = (Abs x (subst_ltrm_ty lamb Y T2))"
| "subst_ltrm_ty (Lambda t T) Y T2 = Lambda (t[Y \<mapsto>\<^sub>\<tau> T2]) (T[Y \<mapsto> T2]\<^sub>\<tau>)"
  apply(finite_guess add: abs_fresh)+
  apply(rule TrueI)+
  apply(simp add: abs_fresh type_subst_fresh)+
  by(fresh_guess add: type_subst_fresh abs_fresh)+

lemma subst_trm_ty_eqvt[eqvt]:
  fixes pi::"vrs prm" and t::"trm" and lt::"ltrm"
  shows "pi\<bullet>(t[X \<mapsto>\<^sub>\<tau> T]) = (pi\<bullet>t)[(pi\<bullet>X) \<mapsto>\<^sub>\<tau> (pi\<bullet>T)]"
        "pi\<bullet>(subst_ltrm_ty lt X T) = subst_ltrm_ty (pi\<bullet>lt) (pi\<bullet>X) (pi\<bullet>T)"
  by(nominal_induct t and lt avoiding: X T rule: trm_ltrm.strong_inducts)
    (perm_simp add: fresh_bij subst_eqvt)+

section \<open>Evaluation\<close>

inductive 
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longmapsto> _" [60,60] 60)
where
  E_Abs         : "\<lbrakk> x \<sharp> v; val v \<rbrakk> \<Longrightarrow> (\<lambda>x:T. t) \<cdot> v \<longmapsto> t[x \<mapsto> v]"
| E_TApp [intro]: "t \<longmapsto> t' \<Longrightarrow> (t \<cdot>\<^sub>\<tau> T) \<longmapsto> (t' \<cdot>\<^sub>\<tau> T)"
| E_App1 [intro]: "t \<longmapsto> t' \<Longrightarrow> t \<cdot> u \<longmapsto> t' \<cdot> u"
| E_App2 [intro]: "\<lbrakk> val v; t \<longmapsto> t' \<rbrakk> \<Longrightarrow> v \<cdot> t \<longmapsto> v \<cdot> t'"
| E_TAbs        : "X \<sharp> T \<Longrightarrow> ((\<lambda>X<:B. t) \<cdot>\<^sub>\<tau> T) \<longmapsto> (t[X \<mapsto>\<^sub>\<tau> T])"

equivariance eval

section \<open>Subtyping\<close>

inductive 
  subtype_of :: "env \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"   ("_\<turnstile>_<:_" [100,100,100] 100)
where
  SA_Top[intro]:       "\<Gamma> \<turnstile> T <: Top"
| SA_refl_TVar[intro]: "\<lbrakk>X \<in> ty_dom \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Tvar X <: Tvar X"
| SA_TVar[intro]:      "\<lbrakk>X \<in> ty_dom \<Gamma>; extract_subtype X \<Gamma> = Some T\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Tvar X <: T"
| SA_trans[intro]:     "\<lbrakk>\<Gamma> \<turnstile> R <: S; \<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> R <: T"
| SA_captr[intro]:     "\<Gamma> \<turnstile> T <: (C \<triangleright> T)"
| SA_capti[intro]:     "\<lbrakk>\<Gamma> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (C \<triangleright> S) <: T"
| SA_arrow[intro]:     "\<lbrakk>\<Gamma> \<turnstile> S\<^sub>2 <: S\<^sub>1; ((VarB x S\<^sub>2) # \<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>2\<rbrakk> \<Longrightarrow> 
                         \<Gamma> \<turnstile> (CapAbs x (S\<^sub>1 \<rightarrow> T\<^sub>1)) <: (CapAbs x (S\<^sub>2 \<rightarrow> T\<^sub>2))" 
| SA_all[intro]:       "\<lbrakk>\<Gamma> \<turnstile> S\<^sub>2 <: S\<^sub>1; ((VarB x S\<^sub>2) # \<Gamma>) \<turnstile> T\<^sub>1 <: T\<^sub>2\<rbrakk> \<Longrightarrow> 
                        \<Gamma> \<turnstile> (\<forall>X<:S\<^sub>1. T\<^sub>1) <: (\<forall>X<:S\<^sub>2. T\<^sub>2)"




end
