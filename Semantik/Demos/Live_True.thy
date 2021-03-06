theory Live_True
imports "HOL-Library.While_Combinator" Vars Big_Step Com
begin

subsection "True Liveness Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = (if x \<in> X then vars a \<union> (X - {x}) else X)" |
"L (c\<^sub>1;; c\<^sub>2) X = L c\<^sub>1 (L c\<^sub>2 X)" |
"L (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> L c\<^sub>1 X \<union> L c\<^sub>2 X" |
"L (WHILE b DO c) X = lfp(\<lambda>Y. vars b \<union> X \<union> L c Y)"

lemma my_mono_L: "mono (L c)"
proof(induction c)
  case (If b c1 c2)
  then show ?case 
    unfolding mono_def 
    using L.simps(4)[of b c1 c2 ] apply simp
    by (meson subset_trans sup_ge1 sup_ge2)
next
  case (While b c)
  then show ?case 
    unfolding mono_def 
    using L.simps(5)[of b c] apply simp
    thm dual_order.refl sup.mono
    by (meson dual_order.refl lfp_mono sup.mono)
qed (auto simp add: mono_def)

lemma L_mono: "mono (L c)" 
proof-
  have "X \<subseteq> Y \<Longrightarrow> L c X \<subseteq> L c Y" for X Y
  proof(induction c arbitrary: X Y)
    case (While b c)
    show ?case
    proof(simp, rule lfp_mono)
      fix Z show "vars b \<union> X \<union> L c Z \<subseteq> vars b \<union> Y \<union> L c Z"
        using While by auto
    qed
  next
    case If thus ?case by(auto simp: subset_iff)
  qed auto
  thus ?thesis by(rule monoI)
qed

lemma mono_union_L:
  "mono (\<lambda>Y. X \<union> L c Y)"
by (metis (no_types) L_mono mono_def order_eq_iff set_eq_subset sup_mono)

lemma L_While_unfold:
  "L (WHILE b DO c) X = vars b \<union> X \<union> L c (L (WHILE b DO c) X)"
by(metis lfp_unfold[OF mono_union_L] L.simps(5))

lemma L_While_pfp: "L c (L (WHILE b DO c) X) \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

lemma L_While_vars: "vars b \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

lemma L_While_X: "X \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

text\<open>Disable @{text "L WHILE"} equation and reason only with @{text "L WHILE"} constraints:\<close>
declare L.simps(5)[simp del]

lemma i: "mono f \<Longrightarrow> f p \<subseteq> p \<Longrightarrow> (f^^i)({}) \<subseteq> p"
proof(induction i)
case 0
  then show ?case by simp
next
  case (Suc i)
  then have "(f ^^ i) {} \<subseteq> p" by simp
  from this Suc.prems(1) 
  have "(f ^^ Suc i) {} \<subseteq> f p" unfolding mono_def by simp
  from this Suc.prems(2) show ?case by simp
qed

subsection "Correctness"

theorem L_correct:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (c,t) \<Rightarrow> t' & s' = t' on X"
proof (induction arbitrary: X t rule: big_step_induct)
  case Skip then show ?case by auto
next
  case Assign then show ?case
    by (auto simp: ball_Un)
next
  case (Seq c1 s1 s2 c2 s3 X t1)
  from Seq.IH(1) Seq.prems obtain t2 where
    t12: "(c1, t1) \<Rightarrow> t2" and s2t2: "s2 = t2 on L c2 X"
    by simp blast
  from Seq.IH(2)[OF s2t2] obtain t3 where
    t23: "(c2, t2) \<Rightarrow> t3" and s3t3: "s3 = t3 on X"
    by auto
  show ?case using t12 t23 s3t3 by auto
next
  case (IfTrue b s c1 s' c2)
  hence "s = t on vars b" and "s = t on L c1 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfTrue(1) have "bval b t" by simp
  from IfTrue.IH[OF \<open>s = t on L c1 X\<close>] obtain t' where
    "(c1, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using \<open>bval b t\<close> by auto
next
  case (IfFalse b s c2 s' c1)
  hence "s = t on vars b" "s = t on L c2 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  from IfFalse.IH[OF \<open>s = t on L c2 X\<close>] obtain t' where
    "(c2, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using \<open>~bval b t\<close> by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t"
    by (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  thus ?case using WhileFalse.prems L_While_X[of X b c] by auto
next
  case (WhileTrue b s1 c s2 s3 X t1)
  let ?w = "WHILE b DO c"
  from \<open>bval b s1\<close> WhileTrue.prems have "bval b t1"
    by (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  have "s1 = t1 on L c (L ?w X)" using  L_While_pfp WhileTrue.prems
    by (blast)
  from WhileTrue.IH(1)[OF this] obtain t2 where
    "(c, t1) \<Rightarrow> t2" "s2 = t2 on L ?w X" by auto
  from WhileTrue.IH(2)[OF this(2)] obtain t3 where "(?w,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with \<open>bval b t1\<close> \<open>(c, t1) \<Rightarrow> t2\<close> show ?case by auto
qed

lemma s: "L c X \<subseteq> rvars c \<union> X"
proof(induction c arbitrary: X)
  case (While b c)
  let ?pfp = "vars b \<union> rvars c \<union> X"
  from While.IH[of ?pfp]
  have "(\<lambda>Y. vars b \<union> X \<union> L c Y) ?pfp \<subseteq> ?pfp" by auto
  then have "lfp (\<lambda>Y. vars b \<union> X \<union> L c Y) \<subseteq> ?pfp" 
    using lfp_lowerbound by metis
  from this L.simps(5) show ?case by simp
qed auto
     
lemma "Vw = vars b \<union> rvars c \<union> X \<Longrightarrow> P \<subseteq> Vw \<Longrightarrow> 
       (\<lambda>Y. vars b \<union> X \<union> L c Y) P \<subseteq> Vw" 
  using s by blast

subsection "Executability"

lemma L_subset_vars: "L c X \<subseteq> rvars c \<union> X"
proof(induction c arbitrary: X)
  case (While b c)
  have "lfp(\<lambda>Y. vars b \<union> X \<union> L c Y) \<subseteq> vars b \<union> rvars c \<union> X"
    using While.IH[of "vars b \<union> rvars c \<union> X"]
    by (auto intro!: lfp_lowerbound)
  thus ?case by (simp add: L.simps(5))
qed auto

text\<open>Make @{const L} executable by replacing @{const lfp} with the @{const
while} combinator from theory @{theory "HOL-Library.While_Combinator"}. The @{const while}
combinator obeys the recursion equation
@{thm[display] While_Combinator.while_unfold[no_vars]}
and is thus executable.\<close>

lemma L_While: fixes b c X
assumes "finite X" defines "f == \<lambda>Y. vars b \<union> X \<union> L c Y"
shows "L (WHILE b DO c) X = while (\<lambda>Y. f Y \<noteq> Y) f {}" (is "_ = ?r")
proof -
  let ?V = "vars b \<union> rvars c \<union> X"
  have "lfp f = ?r"
  proof(rule lfp_while[where C = "?V"])
    show "mono f" by(simp add: f_def mono_union_L)
  next
    fix Y show "Y \<subseteq> ?V \<Longrightarrow> f Y \<subseteq> ?V"
      unfolding f_def using L_subset_vars[of c] by blast
  next
    show "finite ?V" using \<open>finite X\<close> by simp
  qed
  thus ?thesis by (simp add: f_def L.simps(5))
qed

lemma L_While_let: "finite X \<Longrightarrow> L (WHILE b DO c) X =
  (let f = (\<lambda>Y. vars b \<union> X \<union> L c Y)
   in while (\<lambda>Y. f Y \<noteq> Y) f {})"
by(simp add: L_While)

lemma L_While_set: "L (WHILE b DO c) (set xs) =
  (let f = (\<lambda>Y. vars b \<union> set xs \<union> L c Y)
   in while (\<lambda>Y. f Y \<noteq> Y) f {})"
by(rule L_While_let, simp)

text\<open>Replace the equation for @{text "L (WHILE \<dots>)"} by the executable @{thm[source] L_While_set}:\<close>
lemmas [code] = L.simps(1-4) L_While_set
text\<open>Sorry, this syntax is odd.\<close>

text\<open>A test:\<close>
lemma "(let b = Less (N 0) (V ''y''); c = ''y'' ::= V ''x'';; ''x'' ::= V ''z''
  in L (WHILE b DO c) {''y''}) = {''x'', ''y'', ''z''}"
by eval


subsection "Limiting the number of iterations"

text\<open>The final parameter is the default value:\<close>

fun iter :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter f 0 p d = d" |
"iter f (Suc n) p d = (if f p = p then p else iter f n (f p) d)"

text\<open>A version of @{const L} with a bounded number of iterations (here: 2)
in the WHILE case:\<close>

fun Lb :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"Lb SKIP X = X" |
"Lb (x ::= a) X = (if x \<in> X then X - {x} \<union> vars a else X)" |
"Lb (c\<^sub>1;; c\<^sub>2) X = (Lb c\<^sub>1 \<circ> Lb c\<^sub>2) X" |
"Lb (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> Lb c\<^sub>1 X \<union> Lb c\<^sub>2 X" |
"Lb (WHILE b DO c) X = iter (\<lambda>A. vars b \<union> X \<union> Lb c A) 2 {} (vars b \<union> rvars c \<union> X)"

text\<open>@{const Lb} (and @{const iter}) is not monotone!\<close>
lemma "let w = WHILE Bc False DO (''x'' ::= V ''y'';; ''z'' ::= V ''x'')
  in \<not> (Lb w {''z''} \<subseteq> Lb w {''y'',''z''})"
by eval

lemma lfp_subset_iter:
  "\<lbrakk> mono f; \<And>X. f X \<subseteq> f' X; lfp f \<subseteq> D \<rbrakk> \<Longrightarrow> 
    lfp f \<subseteq> iter f' n A D"
proof(induction n arbitrary: A)
  case 0 thus ?case by simp
next
  case Suc thus ?case by simp (metis lfp_lowerbound)
qed

lemma "L c X \<subseteq> Lb c X"
proof(induction c arbitrary: X)
  case (While b c)
  let ?f  = "\<lambda>A. vars b \<union> X \<union> L  c A"
  let ?fb = "\<lambda>A. vars b \<union> X \<union> Lb c A"
  show ?case
  proof (simp add: L.simps(5), rule lfp_subset_iter[OF mono_union_L])
    show "!!X. ?f X \<subseteq> ?fb X" using While.IH by blast
    show "lfp ?f \<subseteq> vars b \<union> rvars c \<union> X"
      by (metis (full_types) L.simps(5) L_subset_vars rvars.simps(5))
  qed
next
  case (Seq c1 c2) 
  from my_mono_L[of c1] Seq.IH(2)[of X]
  have " L c1 (L c2 X) \<subseteq> L c1 (Lb c2 X)" 
    unfolding mono_def by simp
  from this Seq.IH(1)[of "(Lb c2 X)"]      
  show ?case by simp
qed auto

subsection \<open>My notes\<close>

lemma dec:
  assumes 1: "mono f"
  assumes 2: "finite C"
  assumes 3: "(\<And>X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C)"
  assumes 4: "X \<subseteq> C"
  assumes 5: " s \<subseteq> f s \<and> f s \<subseteq> C "
  assumes 6: "f s \<noteq> s"
  shows "(f s, s) \<in> measure (\<lambda>X. card (C - X))"
proof -
  from 5 6 have 7: "s \<subset> f s" by auto
  from this 5 have "C - s \<supset> C - f s " by blast
  from this 2 have "card (C - s) > card (C - f s)" 
    by (simp add: psubset_card_mono)
  from this show ?thesis by simp
qed

lemma while_unfold: 
  "while b c s = (if b s then while b c (c s) else s)"
  using  While_Combinator.while_unfold by metis

lemma while_induct:
 assumes "wf R"
 assumes "I s0"
 assumes STEP: "\<And> s. I s \<Longrightarrow> b s \<Longrightarrow> I (c s) \<and> (c s,s) \<in> R"
 assumes CONS: "\<And> s. I s \<Longrightarrow> \<not> b s \<Longrightarrow> P s"
 shows "P (while b c s0)"
  using assms(1-2)  
proof(induction s0)
 case (less s)
 then show ?case
  apply(subst while_unfold)
  apply auto
  apply (rule less.IH)
  using less.prems STEP apply auto[2]
  using less.prems CONS apply blast
  done
qed

lemma 
  assumes "mono f"
  assumes "finite C"
  assumes "(\<And> X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C)"
  shows "lfp(f) = while (\<lambda>X. f X \<noteq> X) f {}" 
  apply(rule  while_induct[of "measure (\<lambda> X. card (C - X))"  
                      "\<lambda> X. X \<subseteq> C \<and> X \<subseteq> lfp(f) \<and> X \<subseteq> f X" 
                      "{}" "(\<lambda>X. f X \<noteq> X)" f 
                      "\<lambda> Y. lfp(f) = Y" ])
     apply auto[1]
    apply blast 
  apply(rule conjI)
   apply (metis assms(1) assms(3) lfp_unfold mono_def)
  apply (metis assms(1) assms(2) assms(3) dec)
  by (simp add: lfp_lowerbound subset_antisym)
  
  




end