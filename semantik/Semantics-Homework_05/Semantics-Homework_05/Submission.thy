theory Submission
  imports Defs
begin

type_synonym ('q,'l) lts = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"

inductive word :: "('q,'l) lts \<Rightarrow> 'q \<Rightarrow> 'l list \<Rightarrow> 'q \<Rightarrow> bool" for \<delta> where
  empty: "word \<delta> q [] q"
| prepend: "\<lbrakk>\<delta> q l p; word \<delta> p ls r\<rbrakk> \<Longrightarrow> word \<delta> q (l#ls) r"

declare word.intros[simp,intro]

type_synonym effect = "state \<rightharpoonup> state"
type_synonym 'q cfg = "('q,effect) lts"

fun eff_list :: "effect list \<Rightarrow> state \<rightharpoonup> state" where
"eff_list [] s = Some s" |
"eff_list (e # es) s = (
  case (e s) of 
    None \<Rightarrow> None | 
    Some s' \<Rightarrow> eff_list es s'
)"

inductive cfg :: "com cfg" where
  cfg_assign: "cfg (x ::= a) (\<lambda>s. Some (s(x:=aval a s))) (SKIP)"
| cfg_Seq1:   "cfg (SKIP;;c) (\<lambda>s. Some s) c"
| cfg_Seq2:   "cfg c1 e c1' \<Longrightarrow> cfg (c1;;c2) e (c1';;c2)"
| cfg_IfTrue: 
   "cfg (IF b THEN c1 ELSE c2) (\<lambda>s. if bval b s then Some s else None) c1"
| cfg_IfFlse: 
   "cfg (IF b THEN c1 ELSE c2) (\<lambda>s. if bval b s then None else Some s) c2"
| cfg_While:  "cfg (WHILE b DO c) (\<lambda>s. Some s) (IF b THEN c ;; (WHILE b DO c) ELSE SKIP)"

(* step theorem *)
lemma eq_step1: 
 "cs \<rightarrow> cs' \<Longrightarrow> (c,s) = cs \<Longrightarrow> (c',s') = cs' \<Longrightarrow> (\<exists>e. cfg c e c' \<and> e s = Some s')"
  by (induction arbitrary: c s c' s' rule: small_step.induct) (fastforce intro: cfg.intros)+

lemma eq_step_aux: "cfg c e c' \<Longrightarrow> e s = Some s'  \<Longrightarrow> (c, s) \<rightarrow> (c', s')"
proof(induction c e c' arbitrary: s s' rule: cfg.induct)
  case (cfg_IfTrue b s c1 c2)
  then show ?case 
    by (metis option.distinct(1) option.sel small_step.IfTrue)
next
case (cfg_IfFlse b s c1 c2)
  then show ?case
    by (metis option.distinct(1) option.inject small_step.IfFalse)
qed blast+

lemma eq_step2:
 "\<exists>e. cfg c e c' \<and> e s = Some s' \<Longrightarrow> (c, s) \<rightarrow> (c', s')"
  using eq_step_aux by blast
  
theorem eq_step: "(c,s) \<rightarrow> (c',s') \<longleftrightarrow> (\<exists>e. cfg c e c' \<and> e s = Some s')"
  by (meson eq_step1 eq_step2)

(* path theorem *)
lemma eq_path1: "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> (\<exists>\<pi>. word cfg c \<pi> c' \<and> eff_list \<pi> s = Some s')"
proof(induction rule: star_induct)
  case (refl a b) then show ?case by auto 
next
  case (step a b a b a b) then show ?case using eq_step by auto
qed

lemma eq_path2_aux: "word cfg c \<pi> c' \<Longrightarrow> eff_list \<pi> s = Some s' \<Longrightarrow> (c,s) \<rightarrow>* (c',s')"
proof(induction arbitrary: s s' rule: word.induct)
  case (empty q) then show ?case by auto
next
  case (prepend q l p ls r)
  then show ?case by(auto split: option.splits) (meson  eq_step_aux star.simps)
qed

lemma eq_path2: "(\<exists>\<pi>. word cfg c \<pi> c' \<and> eff_list \<pi> s = Some s') \<Longrightarrow> (c,s) \<rightarrow>* (c',s')"
  using eq_path2_aux by blast


theorem eq_path: "(c,s) \<rightarrow>* (c',s') \<longleftrightarrow> (\<exists>\<pi>. word cfg c \<pi> c' \<and> eff_list \<pi> s = Some s')"
  using eq_path1 eq_path2 by blast

end