theory First_Steps
  imports Main
begin

ML {*
3 + 4
*}

(* Remember we need " for this symbol *)
ML \<open> 
3 + 4
\<close>

lemma test:
shows True
ML_prf \<open> writeln "Trivial!" \<close>
  oops

ML \<open>writeln (@{make_string} 1)\<close>

ML \<open>if 0 = 1 then true else (error "foo")\<close>

ML \<open>I 1\<close>

ML \<open>K I\<close>

ML \<open>
val pretty_term = Syntax.pretty_term
val pwriteln = Pretty.writeln

fun x |> f = f x

fun apply_fresh_args f ctxt =
  f |> fastype_of
    |> binder_types
    |> map (pair "z")
    |> Variable.variant_frees ctxt [f]
    |> map Free    
    |> curry list_comb f

\<close>


ML \<open>
let
 val trm = @{term "P::nat \<Rightarrow> int \<Rightarrow> unit \<Rightarrow> bool"}
 val ctxt = @{context}
in
 apply_fresh_args trm ctxt
  |> pretty_term ctxt
  |> pwriteln
end
\<close>

ML \<open>Context.theory_name @{theory}\<close>

thm eq_reflection
thm refl[THEN eq_reflection]

subsection \<open>Printing\<close>

ML \<open>
fun pretty_thm_no_vars ctxt thm =
let
 val ctxt' = Config.put show_question_marks false ctxt
in
 pretty_term ctxt' (Thm.prop_of thm)
end

fun pretty_terms ctxt trms =
Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))
\<close>

subsection \<open>Tactic reasoning\<close>

lemma disj_swap:
  shows "P \<or> Q \<Longrightarrow> Q \<or> P"
apply(erule disjE)
apply(rule disjI2)
apply(assumption)
apply(rule disjI1)
apply(assumption)
  done

ML \<open>
let
 val ctxt = @{context}
 val goal = @{prop "P \<or> Q \<Longrightarrow> Q \<or> P"}
in
 Goal.prove ctxt ["P", "Q"] [] goal
 (fn _ => eresolve_tac @{context} [@{thm disjE}] 1
          THEN resolve_tac @{context} [@{thm disjI2}] 1
          THEN assume_tac @{context} 1
          THEN resolve_tac @{context} [@{thm disjI1}] 1
          THEN assume_tac @{context} 1)
end

\<close>

ML \<open>
fun foo_tac ctxt =
 (eresolve_tac ctxt [@{thm disjE}] 1
  THEN resolve_tac ctxt [@{thm disjI2}] 1
  THEN assume_tac ctxt 1
  THEN resolve_tac ctxt [@{thm disjI1}] 1
  THEN assume_tac ctxt 1)

fun foo_tac' ctxt =
 (eresolve_tac ctxt [@{thm disjE}]
  THEN' resolve_tac ctxt [@{thm disjI2}]
  THEN' assume_tac ctxt
  THEN' resolve_tac ctxt [@{thm disjI1}]
  THEN' assume_tac ctxt)
\<close>

lemma
shows "P1 \<or> Q1 \<Longrightarrow> Q1 \<or> P1"
and "P2 \<or> Q2 \<Longrightarrow> Q2 \<or> P2"
apply(tactic \<open>foo_tac' @{context} 2\<close>)
apply(tactic \<open>foo_tac' @{context} 1\<close>)
done

lemma
shows "\<lbrakk>P \<or> Q;P \<or> Q\<rbrakk> \<Longrightarrow> Q \<or> P"
apply(raw_tactic \<open>foo_tac' @{context} 1\<close>)
back
  sorry

lemma
shows "P \<or> Q \<Longrightarrow> Q \<or> P"
apply(tactic \<open>foo_tac @{context}\<close>)
done

thm disjI1

ML \<open>
fun print_ss ctxt ss =
let
val {simps, congs, procs, ...} = Raw_Simplifier.dest_ss ss
fun name_sthm (nm, thm) =
Pretty.enclose (nm ^ ": ") "" [pretty_thm_no_vars ctxt thm]
fun name_cthm ((_, nm), thm) =
Pretty.enclose (nm ^ ": ") "" [pretty_thm_no_vars ctxt thm]
fun name_trm (nm, trm) =
Pretty.enclose (nm ^ ": ") "" [pretty_terms ctxt trm]
val pps = [Pretty.big_list "Simplification rules:" (map name_sthm simps),
Pretty.big_list "Congruences rules:" (map name_cthm congs),
Pretty.big_list "Simproc patterns:" (map name_trm procs)]
in
pps |> Pretty.chunks
|> pwriteln
end
\<close>

ML \<open>
print_ss @{context} empty_ss
\<close>


lemma
shows "True"
and "t = t"
and "t \<equiv> t"
and "False \<Longrightarrow> Foo"
and "\<lbrakk>A; B; C\<rbrakk> \<Longrightarrow> A"
apply(tactic \<open>ALLGOALS (simp_tac (put_simpset HOL_basic_ss @{context}))\<close>)
done
declare [[ML_print_depth = 200]]



end