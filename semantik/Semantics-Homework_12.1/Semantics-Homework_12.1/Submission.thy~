theory Submission
  imports Defs
begin

paragraph \<open>Arithmetic Expressions\<close>

datatype pval = Iv int | Rv real

datatype val = Ia "int \<Rightarrow> int" | Ra "int \<Rightarrow> real"

type_synonym vname = string

type_synonym state = "vname \<Rightarrow> val"

datatype aexp =  Ic int | Rc real | Vidx vname aexp | Plus aexp aexp

inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> pval \<Rightarrow> bool" where
  taval_Ic: "taval (Ic i) s (Iv i)" |
  taval_Rc: "taval (Rc r) s (Rv r)" |
  taval_PlusInt: "taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2)
   \<Longrightarrow> taval (Plus a1 a2) s (Iv(i1+i2))" |
  taval_PlusReal: "taval a1 s (Rv r1) \<Longrightarrow> taval a2 s (Rv r2)
   \<Longrightarrow> taval (Plus a1 a2) s (Rv(r1+r2))" |
  taval_Ia: "taval i s (Iv idx) \<Longrightarrow> s a = Ia f \<Longrightarrow>
             taval (Vidx a i) s (Iv (f idx))" |
  taval_Ra: "taval i s (Iv idx) \<Longrightarrow> s a = Ra f \<Longrightarrow>
             taval (Vidx a i) s (Rv (f idx))"

inductive_cases taval_elims:
  "taval (Ic i) s v"  "taval (Rc i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"
  \<comment> \<open>New\<close>
  "taval (Vidx x i) s v"

paragraph "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

inductive tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
"tbval (Bc v) s v" |
"tbval b s bv \<Longrightarrow> tbval (Not b) s (\<not> bv)" |
"tbval b1 s bv1 \<Longrightarrow> tbval b2 s bv2 \<Longrightarrow> tbval (And b1 b2) s (bv1 & bv2)" |
"taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2) \<Longrightarrow> tbval (Less a1 a2) s (i1 < i2)" |
"taval a1 s (Rv r1) \<Longrightarrow> taval a2 s (Rv r2) \<Longrightarrow> tbval (Less a1 a2) s (r1 < r2)"

paragraph "Syntax of Commands"

datatype
  com = SKIP 
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)
\<comment> \<open>New:\<close>
      | AssignIdx vname aexp aexp       ("_[_] ::= _" [1000, 0, 61] 61)
      | ArrayCpy vname vname    ("_[] ::= _" [1000, 1000] 61)
      | ArrayClear vname        ("CLEAR _[]" [1000] 61)

paragraph "Small-Step Semantics of Commands"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
  Seq2:   "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |
  IfTrue:  "tbval b s True \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
  IfFalse: "tbval b s False \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |
  While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |
  \<comment> \<open>New:\<close>
  AssignIdxI: "taval v s (Iv iv) \<Longrightarrow> taval i s (Iv idx) \<Longrightarrow> s a = Ia f \<Longrightarrow> 
               (a[i] ::= v,s) \<rightarrow> (SKIP,s(a := (Ia (f(idx := iv)))))" |
  AssignIdxR: "taval v s (Rv rv) \<Longrightarrow> taval i s (Iv idx) \<Longrightarrow> s a = Ra f \<Longrightarrow> 
               (a[i] ::= v,s) \<rightarrow> (SKIP,s(a := (Ra (f(idx := rv)))))" |
  CopyI: "s a = Ia f1 \<Longrightarrow> s b = Ia f2 \<Longrightarrow> (a[] ::= b,s) \<rightarrow> (SKIP,s(a := Ia f2))" |
  CopyR: "s a = Ra f1 \<Longrightarrow> s b = Ra f2 \<Longrightarrow> (a[] ::= b,s) \<rightarrow> (SKIP,s(a := Ra f2))" |
  ClearI: "s a = Ia f \<Longrightarrow> (CLEAR a[],s) \<rightarrow> (SKIP,s(a := Ia (\<lambda>x.0)))" |
  ClearR: "s a = Ra f \<Longrightarrow> (CLEAR a[],s) \<rightarrow> (SKIP,s(a := Ra (\<lambda>x.0)))"

lemmas small_step_induct = small_step.induct[split_format(complete)]

paragraph "The Type System"

datatype ty = Ity | Rty

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> Ic i : Ity" |
Rc_ty: "\<Gamma> \<turnstile> Rc r : Rty" |
Plus_ty: "\<Gamma> \<turnstile> a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Plus a1 a2 : \<tau>" |
\<comment> \<open>New:\<close>
Vidx_Ity: "\<Gamma> \<turnstile> i : Ity \<Longrightarrow> \<Gamma> a = Ity \<Longrightarrow> \<Gamma> \<turnstile> (Vidx a i): Ity" |
Vidx_Rty: "\<Gamma> \<turnstile> i : Ity \<Longrightarrow> \<Gamma> a = Rty \<Longrightarrow> \<Gamma> \<turnstile> (Vidx a i): Rty"

declare atyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> Ic i : \<tau>" "\<Gamma> \<turnstile> Rc r : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>" "\<Gamma> \<turnstile> Vidx x i : \<tau>"


text\<open>Warning: the ``:'' notation leads to syntactic ambiguities,
i.e. multiple parse trees, because ``:'' also stands for set membership.
In most situations Isabelle's type system will reject all but one parse tree,
but will still inform you of the potential ambiguity.\<close>

inductive btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<turnstile>" 50)
where
B_ty: "\<Gamma> \<turnstile> Bc v" |
Not_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> Not b" |
And_ty: "\<Gamma> \<turnstile> b1 \<Longrightarrow> \<Gamma> \<turnstile> b2 \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2" |
Less_ty: "\<Gamma> \<turnstile> a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2"

declare btyping.intros [intro!]
inductive_cases [elim!]: "\<Gamma> \<turnstile> Not b" "\<Gamma> \<turnstile> And b1 b2" "\<Gamma> \<turnstile> Less a1 a2"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c" |
AssignIdx_ty: "\<Gamma> \<turnstile> i : Ity \<Longrightarrow> \<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> x = \<tau> \<Longrightarrow> \<Gamma> \<turnstile> x[i] ::= a" |
Clear_ty: "\<Gamma> \<turnstile> CLEAR x[]" |
Copy_ty: "\<Gamma> x = \<tau> \<Longrightarrow> \<Gamma> y = \<tau> \<Longrightarrow>  \<Gamma> \<turnstile> x[] ::= y"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"
  \<comment> \<open>New\<close>
  "\<Gamma> \<turnstile> x[i] ::= a"
  "\<Gamma> \<turnstile> CLEAR x[]"
  "\<Gamma> \<turnstile> x[] ::= y"

paragraph "Well-typed Programs Do Not Get Stuck"

fun ptype :: "pval \<Rightarrow> ty" where
  "ptype (Iv i) = Ity" |
  "ptype (Rv r) = Rty"

fun type :: "val \<Rightarrow> ty" where
  "type (Ia i) = Ity" |
  "type (Ra r) = Rty"

lemma ptype_eq_Ity[simp]: "ptype v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
  by (cases v) simp_all

lemma ptype_eq_Rty[simp]: "ptype v = Rty \<longleftrightarrow> (\<exists>r. v = Rv r)"
  by (cases v) simp_all

lemma type_eq_Ity[simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Ia i)"
  by (cases v) simp_all

lemma type_eq_Rty[simp]: "type v = Rty \<longleftrightarrow> (\<exists>r. v = Ra r)"
  by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
  where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

theorem apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> taval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> ptype v = \<tau>"
proof(induction arbitrary: v rule: atyping.induct)
  case (Ic_ty \<Gamma> i)
  then show ?case 
    using ptype_eq_Ity taval_elims(1) by blast
next
  case (Rc_ty \<Gamma> r)
  then show ?case 
    using ptype_eq_Rty taval_elims(2) by blast 
next
  case (Plus_ty \<Gamma> a1 \<tau> a2)
  then show ?case
    by (metis ptype.simps(1) ptype.simps(2) taval_elims(4))
next
  case (Vidx_Ity \<Gamma> i a v)
  from \<open>taval (Vidx a i) s v\<close>  show ?case 
    apply(cases,simp)
    by (metis Vidx_Ity.hyps(2) Vidx_Ity.prems(2) styping_def ty.distinct(1) type.simps(2))
next
case (Vidx_Rty \<Gamma> i a v)
  from \<open>taval (Vidx a i) s v\<close> show ?case 
    apply(cases)
     defer 1
     apply simp
    by (metis Vidx_Rty.hyps(2) Vidx_Rty.prems(2) styping_def ty.distinct(1) type.simps(1))
qed

theorem aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. taval a s v"
proof(induction rule: atyping.induct)
case (Ic_ty \<Gamma> i)
  then show ?case using taval_Ic by auto
next
  case (Rc_ty \<Gamma> r)
  then show ?case using taval_Rc by blast
next
  case (Plus_ty \<Gamma> a1 \<tau> a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2" by blast
  show ?case
  proof (cases v1)
    case Iv
    with Plus_ty v show ?thesis 
      by (metis (full_types)  apreservation ptype.elims ptype_eq_Rty taval_PlusInt taval_PlusReal ty.distinct(2))
  next
    case Rv
    with Plus_ty v show ?thesis
      by (metis (full_types) apreservation ptype.elims ptype_eq_Ity taval_PlusInt taval_PlusReal ty.distinct(2))
  qed
next
case (Vidx_Ity \<Gamma> i a)
  then show ?case 
    by (metis apreservation ptype.elims styping_def taval_Ia ty.distinct(1) type.elims)
next
  case (Vidx_Rty \<Gamma> i a)
then show ?case 
  by (metis apreservation ptype.elims taval_Ia taval_Ra ty.distinct(1) type.elims) 
qed

theorem bprogress: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tbval b s v"
proof(induction rule: btyping.induct)
  case (Less_ty \<Gamma> a1 t a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2"
    by (metis aprogress)
  show ?case
  proof (cases v1)
    case Iv
    with Less_ty v show ?thesis
      by (fastforce intro!: tbval.intros(4) dest!:apreservation)
  next
    case Rv
    with Less_ty v show ?thesis
      by (fastforce intro!: tbval.intros(5) dest!:apreservation)
  qed
qed (auto intro: tbval.intros)
  
theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
 proof(induction rule: ctyping.induct)
case (Skip_ty \<Gamma>)
then show ?case  by simp
next
  case (Seq_ty \<Gamma> c1 c2)
  then show ?case by simp (metis Seq1 Seq2)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where "tbval b s bv" by (metis bprogress)
  show ?case
  proof(cases bv)
    assume "bv"
    with \<open>tbval b s bv\<close> show ?case by simp (metis IfTrue)
  next
    assume "\<not>bv"
    with \<open>tbval b s bv\<close> show ?case by simp (metis IfFalse)
  qed
next
case (While_ty \<Gamma> b c)
  then show ?case by (metis While)
next
  case (AssignIdx_ty \<Gamma> i a \<tau> x)
  from this(1) this(4) 
       aprogress[of \<Gamma> i Ity s] obtain idx where 0: "taval i s (Iv idx)" 
    by (metis apreservation ptype_eq_Ity)
  then show ?case 
  proof(cases "\<tau>")
    case Ity
    obtain iv where 1: "taval a s (Iv iv)" 
      by (metis (mono_tags, hide_lams) AssignIdx_ty.hyps(2) AssignIdx_ty.prems(1) 
                Ity apreservation aprogress ptype.cases ptype.simps(2) ty.distinct(1))
    obtain f where  2: "s x = Ia f" 
      by (metis AssignIdx_ty.hyps(3) AssignIdx_ty.prems(1) Ity styping_def type_eq_Ity) 
    from 0 1 2  show ?thesis 
      by (metis AssignIdxI AssignIdx_ty.hyps(1) AssignIdx_ty.prems(1) apreservation ptype_eq_Ity)
  next
    case Rty
    from this aprogress[of \<Gamma> a Rty s] AssignIdx_ty.prems(1) AssignIdx_ty.hyps(2)
    obtain v where "taval a s v" by blast
    from this apreservation[of \<Gamma> a  Rty s v] AssignIdx_ty.prems(1) AssignIdx_ty.hyps(2)
    obtain rv where 1: "taval a s (Rv rv)" 
      using Rty ptype.elims by blast    
    obtain f where  2: "s x = Ra f" 
      by (metis AssignIdx_ty.hyps(3) AssignIdx_ty.prems(1) Rty styping_def type_eq_Rty)
    from 0 1 2 have 3: "(x[i] ::= a,s) \<rightarrow> (SKIP,s(x := (Ra (f(idx := rv)))))"
      by (simp add: AssignIdxR) 
    show ?thesis using "3" by auto
  qed 
next
  case (Clear_ty \<Gamma> x) then show ?case by (meson ClearI ClearR type.elims) 
next
  case (Copy_ty \<Gamma> x \<tau> y)
then show ?case apply(cases "s x") 
   apply (metis (mono_tags, lifting) CopyI styping_def type_eq_Ity)
   by (metis (mono_tags, lifting) CopyR Copy_ty.prems(1) styping_def type_eq_Rty) 
qed

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induction rule: small_step_induct)
  case (AssignIdxI v s iv i idx a f)
  then show ?case 
  proof -
   have "\<forall>cs. \<Gamma> cs = type (s cs)" by (metis AssignIdxI.prems(2) styping_def)
   then show ?thesis 
   using AssignIdxI.hyps(3) styping_def by auto
 qed
next
  case (AssignIdxR v s rv i idx a f)
  then show ?case  
  proof -
   have "\<forall>cs. \<Gamma> cs = type (s cs)" by (metis AssignIdxR.prems(2) styping_def)
   then show ?thesis 
   using AssignIdxR.hyps(3) styping_def by auto
 qed  
next
  case (CopyI s a f1 b f2)
  then show ?case 
    proof -
   have "\<forall>cs. \<Gamma> cs = type (s cs)" by (metis CopyI.prems(2) styping_def)
   then show ?thesis 
   using CopyI.hyps(1) styping_def by auto
 qed  
next
  case (CopyR s a f1 b f2)
  then show ?case 
   proof -
   have "\<forall>cs. \<Gamma> cs = type (s cs)" by (metis CopyR.prems(2) styping_def)
   then show ?thesis 
   using CopyR.hyps(1) styping_def by auto
 qed  
next
  case (ClearI s a f)
  then show ?case 
  proof -
   have "\<forall>cs. \<Gamma> cs = type (s cs)"  by (metis ClearI.prems(2) styping_def)
   then show ?thesis 
   using ClearI.hyps(1) styping_def by auto
 qed  
next
  case (ClearR s a f)
  then show ?case 
   proof -
   have "\<forall>cs. \<Gamma> cs = type (s cs)"  by (metis ClearR.prems(2) styping_def)
   then show ?thesis 
   using ClearR.hyps(1) styping_def by auto
 qed  
qed auto

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
  by(induct rule: small_step_induct) (auto simp: ctyping.intros)
  
abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y"

corollary type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
apply(induction rule:star_induct)
apply (metis progress)
by (metis styping_preservation ctyping_preservation)

text \<open>Hint: Note that the original proofs are highly automated. Do not expect your proofs
to be quite as automated!
Use Isar. Explicit rule inversion can be helpful. Recall that this can be achieved with
a proof snippet of the following form:\\
\<open>
from \<open>taval a s v\<close> show ?case
  proof cases
\<close>
\<close>

end