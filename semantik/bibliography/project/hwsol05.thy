(*<*)
theory hwsol05
imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Small_Step"
begin
(*>*)

text {* \ExerciseSheet{5}{01.06.2015} *}

text {*
\NumHomework{Dijkstra's Guarded Command Language (12 points)}{08.06.2015}

{\bf Unless indicated otherwise, please give all your proofs in Isar, not
\texttt{apply} style.}

\medskip

In the 1970s, Edsger Dijkstra introduced the guarded command language (GCL), a
nondeterministic programming language featuring a nondeterministic \texttt{if}
command with the syntax
%
\begin{quote}
\begin{verbatim}
if b1 --> c1
 | b2 --> c2
 ...
 | bN --> cN
fi
\end{verbatim}
\end{quote}
%
where \texttt{b1}, \texttt{b2}, \ldots, \texttt{bN} are Boolean conditions and
\texttt{c1}, \texttt{c2}, \ldots, \texttt{cN} are commands. When executing the
statement, an arbitrary branch with a condition that evaluates to true is
selected. If no condition is true, execution simply blocks.

\medskip

To keep things simple, we will have no looping command in our language.
Here is the Isabelle datatype:
*}

datatype gcom =
  Skip
| Ass vname aexp
| Sq gcom gcom
| IfBlock "(bexp \<times> gcom) list"

text {*
First, define the big-step semantics with infix syntax @{text "\<Rightarrow>g"}:
*}

inductive
  big_stepg :: "gcom \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>g" 55) (*<*)
where
  Skip: "(Skip, s) \<Rightarrow>g s"
| Ass: "(Ass x a, s) \<Rightarrow>g s(x := aval a s)"
| Sq: "(c, s) \<Rightarrow>g s' \<Longrightarrow> (c', s') \<Rightarrow>g s'' \<Longrightarrow> (Sq c c', s) \<Rightarrow>g s''"
| IfBlock: "(b, c) \<in> set Gs \<Longrightarrow> bval b s \<Longrightarrow> (c, s) \<Rightarrow>g s' \<Longrightarrow> (IfBlock Gs, s) \<Rightarrow>g s'"
(*>*)

text {*
Use @{file "~~/src/HOL/IMP/Big_Step.thy"} as an inspiration. Remember to give
names to your introduction rules, so that you can refer to each rule by name
in your proofs by rule induction.

\medskip

Like in @{file "~~/src/HOL/IMP/Big_Step.thy"}, we declare the introduction
rules as @{text intro} rules for @{text auto}, @{text blast}, @{text fast},
@{text fastforce}, @{text force}, and @{text extreme_violence}. We also do
some magic with the induction rule to make it more suitable---this is
necessary only because the first argument to @{text "\<Rightarrow>g"} is tupled.
*}

declare big_stepg.intros [intro]

lemmas big_stepg_induct = big_stepg.induct[split_format(complete)]

text {*
This will come in handy later:
*}

inductive_cases SqE: "(Sq c1 c2, s) \<Rightarrow>g t"
inductive_cases IfBlockE: "(IfBlock Gs, s) \<Rightarrow>g t"

thm SqE IfBlockE

text {*
A useful lemma. Prove it:
*}

lemma IfBlock_subset_big_stepg:
  assumes
    Gs: "(IfBlock Gs, s) \<Rightarrow>g s'" and
    Gs': "set Gs \<subseteq> set Gs'"
  shows "(IfBlock Gs', s) \<Rightarrow>g s'" (*<*)
(* Schade! Sledgehammer doesn't work here *)
proof -
  obtain b c where bc: "(b, c) \<in> set Gs" "bval b s" "(c, s) \<Rightarrow>g s'"
    by (rule IfBlockE[OF Gs])
  thus ?thesis
    using Gs' by auto
qed
(*>*)

text {*
Write various schematic lemmas in the style of @{file "~~/src/HOL/IMP/Big_Step.thy"} and
try out your big-step semantics on them. In particular, try to take both branches of
a two-way \texttt{if} block. For this part, you are allowed (indeed, encouraged) to
write your proofs in \textbf{apply} style. *}

schematic_lemma ex1: "(Sq (Ass ''x'' (N 5)) (Ass ''y'' (V ''x'')), s) \<Rightarrow>g ?s'" (*<*)
apply (rule Sq)
 apply (rule Ass)
apply (rule Ass)
done
(*>*)text {* $\qquad\ldots$ *}
thm ex1[simplified]

schematic_lemma ex2: "(IfBlock [(Less (N 4) (N 5), Ass ''x'' (N 2))], s) \<Rightarrow>g ?s'" (*<*)
apply (rule IfBlock)
  apply simp
 apply simp
apply (rule Ass)
done
(*>*)text {* $\qquad\ldots$ *}
thm ex2[simplified]

schematic_lemma ex3a:
  "(IfBlock [(Less (N 4) (N 5), Ass ''x'' (N 2)), (Less (N 6) (N 7), Ass ''x'' (N 3))], s)
   \<Rightarrow>g ?s'" (*<*)
apply (rule IfBlock[of "Less (N 4) (N 5)"])
  apply simp
 apply simp
apply (rule Ass)
done
(*>*)text {* $\qquad\ldots$ *}
thm ex3a[simplified]

schematic_lemma ex3b:
  "(IfBlock [(Less (N 4) (N 5), Ass ''x'' (N 2)), (Less (N 6) (N 7), Ass ''x'' (N 3))], s)
   \<Rightarrow>g ?s'" (*<*)
apply (rule IfBlock[of "Less (N 6) (N 7)"])
  apply simp
 apply simp
apply (rule Ass)
done
(*>*)text {* $\qquad\ldots$ *}
thm ex3b[simplified]

text {*
Is the language deterministic? Prove or disprove.
*}

lemma "(c, s) \<Rightarrow>g s' \<Longrightarrow> (c, s) \<Rightarrow>g s'' \<Longrightarrow> s' = s''" (*<*)
nitpick[card int = 2, card state = 2]
(*
  nitpick[card int = 2, card state = 2]

  nitpick's "potentially spurious counterexample" is genuine:

  Free variables:
    c = IfBlock [(Less (V s\<^sub>1) (V s\<^sub>2), Ass s\<^sub>2 (V s\<^sub>1)), (Less (V s\<^sub>1) (V s\<^sub>2), Skip)]
    s = (\<lambda>x. ?)(s\<^sub>1 := 0, s\<^sub>2 := 1, s\<^sub>3 := 0)
    s' = (\<lambda>x. ?)(s\<^sub>1 := 0, s\<^sub>2 := 1, s\<^sub>3 := 0)
    s'' = (\<lambda>x. ?)(s\<^sub>1 := 0, s\<^sub>2 := 0, s\<^sub>3 := 0)
*)
oops
(*>*)

text {*
Is the language total? Prove or disprove.
*}

lemma "\<exists>s'. (c, s) \<Rightarrow>g s'" (*<*)
(*
  nitpick

  nitpick's "potentially spurious counterexample" is genuine:

  Free variables:
    c = IfBlock []
    s = (\<lambda>x. ?)(s\<^sub>1 := 0)
*)
oops
(*>*)

text {*
Next, define the semantics as a function. In cases where several guard
conditions evaluate to true, it can arbitrarily select a true branch (e.g., the
first true branch). If the program blocks, the function returns @{term None}.
*}

fun big_stepgf :: "gcom \<Rightarrow> state \<Rightarrow> state option" (*<*) where
  "big_stepgf Skip s = Some s"
| "big_stepgf (Ass x a) s = Some (s(x := aval a s))"
| "big_stepgf (Sq c c') s =
   (case big_stepgf c s of
      None => None
    | Some s' => big_stepgf c' s')"
| "big_stepgf (IfBlock []) s = None"
| "big_stepgf (IfBlock ((b, c) # Gs)) s =
   big_stepgf (if bval b s then c else IfBlock Gs) s"
(*>*)

text {*
Specify names for the cases of the induction rule generated for the above
function, to enhance the readability of Isar proofs (i.e., replace @{text "\<dots>"}\ with
appropriate names):
*}

lemmas big_stepgf_induct = big_stepgf.induct[case_names (*<*)Skip Ass Sq IfBlock_Nil IfBlock_Cons(*>*) \<dots>]

text {*
A useful lemma. Prove it:
*}

lemma big_stepgf_Some_imp_ex_inter:
  "big_stepgf (Sq c c') s = Some s'' \<Longrightarrow>
   \<exists>s'. big_stepgf c s = Some s' \<and> big_stepgf c' s' = Some s''" (*<*)
by (metis big_stepgf.simps(3) option.case_eq_if option.distinct(2) option.sel_exhaust)
(*>*)

text {*
Prove or disprove that the function @{const big_stepgf} is sound with respect to the
inductive predicate @{const big_stepg}:
*}

theorem big_stepgf_sound: "big_stepgf c s = Some s' \<Longrightarrow> (c, s) \<Rightarrow>g s'" (*<*)
proof (induction c s arbitrary: s' rule: big_stepgf_induct)
  case (Skip _) thus ?case by auto
next
  case (Ass _ _ _) thus ?case by auto
next
  case (Sq c c' s)
  obtain sa where sa: "big_stepgf c s = Some sa" and s': "big_stepgf c' sa = Some s'"
    using big_stepgf_Some_imp_ex_inter[OF Sq(3)] by fast
  note Sq' = Sq(1,2)[OF sa]
  show ?case
    using Sq'(1) Sq'(2)[OF s'] by blast
next
  case (IfBlock_Nil _) thus ?case by auto
next
  case (IfBlock_Cons b c Gs s)
  show ?case
  proof (cases "bval b s")
    case True
    thus ?thesis
      using IfBlock_Cons by auto
  next
    case False
    hence "big_stepgf (IfBlock Gs) s = Some s'"
      using IfBlock_Cons.prems by simp
    hence "(IfBlock Gs, s) \<Rightarrow>g s'"
      using False IfBlock_Cons.IH(1) by simp
    thus ?thesis
      by (metis IfBlock_subset_big_stepg set_subset_Cons)
  qed
qed
(*>*)

text {*
Hint: If you go for a proof, make sure to use the most appropriate induction principle,
and ask yourself whether you need @{text "arbitrary:"}.

\medskip

Finally, prove or disprove completeness:
*}

lemma big_stepgf_complete: "(c, s) \<Rightarrow>g s' \<Longrightarrow> \<exists>t. big_stepgf c s = Some t"
(*<*)
(*
  nitpick

  nitpick's "potentially spurious counterexample" is genuine:

  Free variables:
    c = IfBlock [(Less (V s\<^sub>1) (V s\<^sub>2), IfBlock []), (Less (V s\<^sub>1) (V s\<^sub>2), Skip)]
    s = (\<lambda>x. ?)(s\<^sub>1 := - 1, s\<^sub>2 := 0, s\<^sub>3 := - 1)
    s' = (\<lambda>x. ?)(s\<^sub>1 := - 1, s\<^sub>2 := 0, s\<^sub>3 := - 1)
*)
oops
(*>*)

text {*
\NumHomework{More GCL (8 points)}{08.06.2015}

{\bf Please give all your proofs in Isar, not \texttt{apply} style.}

\medskip

This is a continuation of the previous homework exercise.

\medskip

Define a notion of program equivalence for GCL:
*}

abbreviation equiv_cg :: "gcom \<Rightarrow> gcom \<Rightarrow> bool" (infix "\<sim>g" 50) (*<*) where
  "c \<sim>g c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow>g t \<longleftrightarrow> (c', s) \<Rightarrow>g t)" (*>*)

text {*
Show that @{text "\<sim>g"} is an equivalence relation:
*}

lemma reflp_equiv_cg: "reflp (op \<sim>g)" (*<*)
  unfolding reflp_def by auto
(*>*)

lemma symp_equiv_cg:"symp (op \<sim>g)" (*<*)
  unfolding symp_def by auto
(*>*)

lemma transpp_equiv_cg: "transp (op \<sim>g)" (*<*)
  unfolding transp_def by auto
(*>*)

text {*
Prove the congruence lemma for @{const Sq}:
*}

(*<*)
lemma Sq_cong1:
  assumes
    c1: "c1 \<sim>g c1'" and
    c2: "c2 \<sim>g c2'"
  shows "(Sq c1 c2, s) \<Rightarrow>g t \<Longrightarrow> (Sq c1' c2', s) \<Rightarrow>g t"
proof -
  assume "(Sq c1 c2, s) \<Rightarrow>g t"
  then obtain s' where "(c1, s) \<Rightarrow>g s'" "(c2, s') \<Rightarrow>g t"
    by (metis SqE)
  hence "(c1', s) \<Rightarrow>g s'" "(c2', s') \<Rightarrow>g t"
    using c1 c2 by metis+
  thus "(Sq c1' c2', s) \<Rightarrow>g t"
    by auto
qed

(*>*)
lemma Sq_cong:
  assumes
    c1: "c1 \<sim>g c1'" and
    c2: "c2 \<sim>g c2'"
  shows "Sq c1 c2 \<sim>g Sq c1' c2'" (*<*)
proof -
  from c1 have c1': "c1' \<sim>g c1" using symp_equiv_cg[unfolded symp_def] by metis
  from c2 have c2': "c2' \<sim>g c2" using symp_equiv_cg[unfolded symp_def] by metis
  show ?thesis
    using Sq_cong1[OF c1 c2] Sq_cong1[OF c1' c2'] symp_equiv_cg[unfolded symp_def]
    by metis
qed

text {* Alternative proof, exploiting the symmetry: *}

lemma sym_prop2:
  assumes
    "\<forall>x y x' y'. P x y x' y' \<longrightarrow> (Q x y \<longrightarrow> Q x' y')" and
    "\<forall>x y x' y'. P x y x' y' \<longrightarrow> P x' y' x y" and
    "P x y x' y'"
  shows "Q x y \<longleftrightarrow> Q x' y'"
using assms by blast

lemma Sq_cong':
  assumes
    c1: "c1 \<sim>g c1'" and
    c2: "c2 \<sim>g c2'"
  shows "Sq c1 c2 \<sim>g Sq c1' c2'"
using sym_prop2[of "\<lambda>c1 c2 c1' c2'. c1 \<sim>g c1' \<and> c2 \<sim>g c2'" _ c1 c2 c1' c2'] Sq SqE c1 c2
by smt
(*>*)

text {*
\NumHomework{Even more GCL (5 \textbf{bonus} points)}{08.06.2015}

{\bf Please give all your proofs in Isar, not \texttt{apply} style.}

\medskip

This is a continuation of the previous homework exercise. \textbf{Warning:}
This is a difficult exercise. Do not spend too much time on it.

\medskip

Prove the congurence lemma for @{const IfBlock}. There are many ways of stating
it. Use whichever style you prefer, including these:
*}

lemma IfBlock_cong_v1:
  assumes allc: "\<forall>(b, (c, c')) \<in> set GGs. c \<sim>g c'"
  shows
    "IfBlock (map (\<lambda>(b, (c, _)). (b, c)) GGs)
     \<sim>g IfBlock (map (\<lambda>(b, (_, c')). (b, c')) GGs)"
(*<*)
proof (intro allI iffI)
  fix s t
  assume "(IfBlock (map (\<lambda>(b, (c, _)). (b, c)) GGs), s) \<Rightarrow>g t"
  then obtain b c where
    bc: "(b, c) \<in> set (map (\<lambda>(b, (c, _)). (b, c)) GGs)" "bval b s" "(c, s) \<Rightarrow>g t"
    using IfBlockE by blast
  then obtain c' where bcc': "(b, (c, c')) \<in> set GGs"
    by auto
  hence cc': "c \<sim>g c'"
    using allc by auto
  hence bc': "(b, c') \<in> set (map (\<lambda>(b, (_, c')). (b, c')) GGs)" "(c', s) \<Rightarrow>g t"
    using bc
    by (metis (mono_tags, lifting) bcc' image_eqI prod.simps(2) set_map)
      (metis bc(3) cc')
  show "(IfBlock (map (\<lambda>(b, (_, c')). (b, c')) GGs), s) \<Rightarrow>g t"
    by (rule IfBlock[OF bc'(1) bc(2) bc'(2)])
next
  (* copy-pasted from above -- not so easy to avoid the duplication without
     stating the theorem differently (e.g. using two or three lists of the
     same length) *)
  fix s t
  assume "(IfBlock (map (\<lambda>(b, (_, c')). (b, c')) GGs), s) \<Rightarrow>g t"
  then obtain b c' where
    bc': "(b, c') \<in> set (map (\<lambda>(b, (_, c')). (b, c')) GGs)" "bval b s" "(c', s) \<Rightarrow>g t"
    using IfBlockE by blast
  then obtain c where bcc': "(b, (c, c')) \<in> set GGs"
    by auto
  hence c'c: "c' \<sim>g c"
    using allc by auto
  hence bc: "(b, c) \<in> set (map (\<lambda>(b, (c, _)). (b, c)) GGs)" "(c, s) \<Rightarrow>g t"
    using bc'
    by (metis (mono_tags, lifting) bcc' image_eqI prod.simps(2) set_map)
      (metis bc'(3) c'c)
  show "(IfBlock (map (\<lambda>(b, (c, _)). (b, c)) GGs), s) \<Rightarrow>g t"
    by (rule IfBlock[OF bc(1) bc'(2) bc(2)])
qed (*>*)

lemma IfBlock_cong_v2:
  assumes len: "length bs = n" "length cs = n" "length cs' = n"
  assumes alli: "\<And>i. i < n \<Longrightarrow> cs ! i \<sim>g cs' ! i"
  shows "IfBlock (zip bs cs) \<sim>g IfBlock (zip bs cs')" (*<*)
proof -
  let ?CCs = "zip cs cs'"
  let ?GGs = "zip bs ?CCs"

  have "\<And>i. i < n \<Longrightarrow> fst (?CCs ! i) \<sim>g snd (?CCs ! i)"
    using len alli by (metis fst_conv nth_zip snd_conv)
  hence "\<forall>(c, c') \<in> set (zip cs cs'). \<forall>s t. (c, s) \<Rightarrow>g t = (c', s) \<Rightarrow>g t"
    using len alli by (auto simp: in_set_conv_nth)
  hence allc: "\<forall>(b, c, c') \<in> set ?GGs. \<forall>s t. (c, s) \<Rightarrow>g t = (c', s) \<Rightarrow>g t"
    by (metis (lifting) case_prodI2 set_zip_rightD)

  have "map (\<lambda>(b, (c, _)). (b, c)) (zip bs (zip cs cs')) = zip bs cs"
    using len by (smt2 case_prod_unfold cond_split_eta map_fst_zip split_conv zip_map2)
  moreover have "map (\<lambda>(b, (_, c')). (b, c')) (zip bs (zip cs cs')) = zip bs cs'"
    using len by (smt2 case_prod_unfold map_eq_conv map_snd_zip zip_map2)
  ultimately show ?thesis
    using IfBlock_cong_v1[OF allc] by auto
qed
(*>*)

text {*
The @{text "!"} operator is syntactic sugar for @{text nth}, defined in @{theory List}.
It returns the $(n - 1)$st element of a list (not the $n$th!).

\medskip

Finally, show that the order of the elements in the guard block list and
any duplicates are irrelevant:
*}

lemma IfBlock_set_eq_cong:
  assumes set: "set Gs = set Gs'"
  shows "IfBlock Gs \<sim>g IfBlock Gs'" (*<*)
proof (intro allI iffI)
  fix s t
  assume "(IfBlock Gs, s) \<Rightarrow>g t"
  thus "(IfBlock Gs', s) \<Rightarrow>g t"
    by (metis IfBlock_subset_big_stepg order_refl set)
next
  fix s t
  assume "(IfBlock Gs', s) \<Rightarrow>g t"
  thus "(IfBlock Gs, s) \<Rightarrow>g t"
    by (metis IfBlock_subset_big_stepg order_refl set)
qed
(*>*)

text {*
\bigskip

The end is the beginning is the *}

end
