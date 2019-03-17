theory Submission
  imports Defs
begin

fun exec :: "com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state \<times> nat" where
"exec SKIP s f = (s, f)"
| "exec (x::=v) s f = (s(x:=aval v s), f)"
| "exec (c1;;c2) s f = (
    let (s, f') = exec c1 s f in exec c2 s f')"
| "exec (IF b THEN c1 ELSE c2) s f =
    (if bval b s then exec c1 s f else exec c2 s f)"
| "exec (WHILE b DO c) s (Suc f) = (
    if bval b s then
      (let (s, f') = exec c s f in
        if f > 0 then exec (WHILE b DO c) s (min f f') else (s, 0)
      ) else (s, Suc f))"
| "exec _ s 0 = (s, 0)"

lemma exec_equiv_bigstep: "(\<exists>f f'. exec c s f = (s', f') \<and> f' > 0) \<longleftrightarrow> (c,s) \<Rightarrow> s'"
  oops

paragraph "Step 1"

fun while_free :: "com \<Rightarrow> bool" where
"while_free SKIP \<longleftrightarrow> True" |
"while_free (Assign v expr) \<longleftrightarrow> True" |
"while_free (Seq c1 c2) \<longleftrightarrow> (while_free c1 \<and> while_free c2)" |
"while_free (If b c1 c2) \<longleftrightarrow> (while_free c1 \<and> while_free c2)" |
"while_free (While b c) \<longleftrightarrow> False"

paragraph "Step 2"

lemma while_not_decrease: 
  "exec c s f = (s',f') \<Longrightarrow> while_free c \<Longrightarrow> f \<le> f'"
proof(induction c s f arbitrary: s' f' rule: exec.induct)
case (2 x v s f)
then show ?case by (simp split: prod.splits)
next
  case (3 c1 c2 s f)
  then show ?case by(force split: prod.splits)
next
case (4 b c1 c2 s f)
  then show ?case by(auto split: if_splits)
qed auto+
  
theorem while_free_fuel: "while_free c \<Longrightarrow> \<exists>f s' f'. exec c s f = (s', f') \<and> f' > 0"
by (metis not_one_le_zero old.prod.exhaust while_not_decrease zero_less_iff_neq_zero)

paragraph "Step 3"

(* We reorder here the goals so that the proof passes by *)

text \<open>We show that the amount of fuel can never increase during an execution.\<close>
lemma exec_fuel_nonincreasing:
  "exec c s f = (s', f') \<Longrightarrow> f' \<le> f"
proof -
  assume "exec c s f = (s', f')"
  then show "f' \<le> f"
  proof(induction c s f arbitrary: s' f' rule: exec.induct) 
    case (3 c1 c2 s f)
      then show ?case by (auto split: prod.splits) (fastforce)
  next
    case (4 b c1 c2 s f) then show ?case by (auto split: if_splits)
  next
    case (5 b c s f)
      then show ?case 
        by(auto simp add: le_Suc_eq split: if_splits prod.splits)
  qed auto+
qed

text \<open>Show this directly with one induction proof (using Isar)\<close>

theorem exec_imp_bigstep: "exec c s f = (s', f') \<Longrightarrow> f' > 0 \<Longrightarrow> (c,s) \<Rightarrow> s'"
proof(induction c s f arbitrary: s' f' rule: exec.induct)
  case (3 c1 c2 s f)
  note prems = this
  from this have "\<exists> si fi. exec c1 s f = (si,fi) \<and> exec c2 si fi = (s',f')" 
    by (metis exec.simps(3) old.prod.exhaust split_conv)
  from this obtain si fi where 
    unfold: "exec c1 s f = (si,fi) \<and> exec c2 si fi = (s',f')" by auto
  from this prems have fipos: "fi > 0" 
    using exec_fuel_nonincreasing by fastforce
  show ?case 
    using fipos prems(1) prems(2) prems(4) unfold by fastforce
next
  case (4 b c1 c2 s f)
  then show ?case by (auto split: if_splits) 
next
  case (5 b c s f)
  then show ?case by (auto split: if_splits prod.splits) (fastforce simp: WhileTrue) 
qed auto+


text \<open>Show the following helpful lemma from which we get the two corollaries below,
which will be useful in the final proof:\<close>
lemma exec_add: 
 "exec c s f = (s', f') \<Longrightarrow> 
  f' > 0 \<Longrightarrow> exec c s (f + k) = (s', f' + k)"
proof(induction c s f arbitrary: s' f' rule: exec.induct)
next
  case (3 c1 c2 s f)
  then show ?case
    using exec_fuel_nonincreasing by (simp split: prod.splits) (fastforce)
next
  case (5 b c s f)
  then show ?case 
    by(auto split: prod.splits if_splits)
      (metis Pair_inject exec.simps(6) min_0R min_add_distrib_left neq0_conv)+
qed auto+

lemma exec_mono:
  "exec c s f = (s', f') \<Longrightarrow> f' > 0 \<Longrightarrow> f1 \<ge> f \<Longrightarrow> \<exists>f2. f2 \<ge> f' \<and> exec c s f1 = (s', f2)"
  by (auto simp: exec_add dest: le_Suc_ex)

lemma exec_mono':
  "exec c s f = (s', f') \<Longrightarrow> f' > 0 \<Longrightarrow> f2 \<ge> f' \<Longrightarrow> \<exists>f1. f1 \<ge> f \<and> exec c s f1 = (s', f2)"
  by (metis exec_add le_Suc_ex le_add_same_cancel1)

text \<open>Use induction and the auxiliary lemmas above.\<close>
                                                                
lemma bigstep_imp_exec_aux: 
 "cs \<Rightarrow> s' \<Longrightarrow> (c,s) = cs \<Longrightarrow> \<exists>f f'. f' > 0 \<and> exec c s f = (s', f')"
proof(induction arbitrary: c s rule: big_step.induct)
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  note seq = this
  from this have first: "\<exists>f f'. 0 < f' \<and> exec c\<^sub>1 s\<^sub>1 f  = (s\<^sub>2, f')" by auto
  from seq have second: "\<exists>f f'. 0 < f' \<and> exec c\<^sub>2 s\<^sub>2 f  = (s\<^sub>3,f')" by auto
  from first obtain f\<^sub>1 f\<^sub>2 where first_cond: "0 < f\<^sub>2 \<and> exec c\<^sub>1 s\<^sub>1 f\<^sub>1  = (s\<^sub>2, f\<^sub>2)" by auto
  from second obtain f\<^sub>3 f\<^sub>4 where second_cond: "0 < f\<^sub>4 \<and> exec c\<^sub>2 s\<^sub>2 f\<^sub>3  = (s\<^sub>3, f\<^sub>4)" by auto
  show ?case
  proof(cases "f\<^sub>2 \<le> f\<^sub>3")
    case True
    from this first_cond exec_mono'[of c\<^sub>1 s\<^sub>1 f\<^sub>1 s\<^sub>2 f\<^sub>2 f\<^sub>3]  show ?thesis 
    by (metis exec.simps(3) local.Seq(5) prod.sel(1) prod.sel(2) second_cond split_conv)
  next
    case False
    from this second_cond exec_mono[of c\<^sub>2 s\<^sub>2 f\<^sub>3 s\<^sub>3 f\<^sub>4 f\<^sub>2] show ?thesis
    by (metis (full_types) Seq.prems exec.simps(3) first_cond nat_le_linear neq0_conv not_le prod.sel(1) prod.sel(2) split_conv) 
  qed
next
  case (WhileFalse b s c)
  then show ?case by (auto split: prod.splits) (meson exec.simps(5) lessI)
next
  case (WhileTrue b s\<^sub>1 d s\<^sub>2 s\<^sub>3)
  note wtrue = this
  from this have first: "\<exists>f f'. 0 < f' \<and> exec d s\<^sub>1 f  = (s\<^sub>2, f')" by auto
  from wtrue have second: "\<exists>f f'. 0 < f' \<and> exec (WHILE b DO d) s\<^sub>2 f  = (s\<^sub>3,f')" by auto
  from first obtain f\<^sub>1 f\<^sub>2 where first_cond: "0 < f\<^sub>2 \<and> exec d s\<^sub>1 f\<^sub>1  = (s\<^sub>2, f\<^sub>2)" by auto
  from second obtain f\<^sub>3 f\<^sub>4 where second_cond: 
   "0 < f\<^sub>4 \<and> exec (WHILE b DO d) s\<^sub>2 f\<^sub>3  = (s\<^sub>3, f\<^sub>4)" by auto
  from first exec_fuel_nonincreasing have f1pos: "f\<^sub>1 > 0"
    using first_cond not_le by blast
  show ?case
  proof(cases "f\<^sub>2 \<le> f\<^sub>3")
    case True
    note f2lf3 = this
    from this first_cond exec_mono'[of d s\<^sub>1 f\<^sub>1 s\<^sub>2 f\<^sub>2 f\<^sub>3] have 
     "\<exists>f1\<ge>f\<^sub>1. exec d s\<^sub>1 f1 = (s\<^sub>2, f\<^sub>3)" by auto
    from this obtain f\<^sub>5 where inst1: "f\<^sub>5 \<ge> f\<^sub>1 \<and> exec d s\<^sub>1 f\<^sub>5 = (s\<^sub>2, f\<^sub>3)" by auto
    from this f1pos have f5pos: "f\<^sub>5 > 0" by auto
    from this inst1  wtrue(1) f1pos  second_cond have 
     "exec (WHILE b DO d) s\<^sub>1 (Suc f\<^sub>5) = exec (WHILE b DO d) s\<^sub>2 (min f\<^sub>3 f\<^sub>5)" 
      by (smt exec.simps(5) f5pos min_def not_le order_le_less split_conv)
    from this have pre: "exec (WHILE b DO d) s\<^sub>1 (Suc f\<^sub>5) = exec (WHILE b DO d) s\<^sub>2 f\<^sub>3" 
      by (metis exec_fuel_nonincreasing inst1 min_def) 
      show ?thesis 
        by (metis Pair_inject WhileTrue.prems pre second_cond)
  next
    case False
    from this second_cond exec_mono[of "(WHILE b DO d)" s\<^sub>2 f\<^sub>3 s\<^sub>3 f\<^sub>4 f\<^sub>2] have
      "\<exists>f2\<ge>f\<^sub>4. exec (WHILE b DO d) s\<^sub>2 f\<^sub>2 = (s\<^sub>3, f2)" by auto
    from this obtain f\<^sub>5 where inst1: 
      "f\<^sub>5 \<ge> f\<^sub>4 \<and> exec (WHILE b DO d) s\<^sub>2 f\<^sub>2 = (s\<^sub>3, f\<^sub>5)" by auto
    from  f1pos first_cond wtrue(1) have
     pre1: "exec (WHILE b DO d) s\<^sub>1 (Suc f\<^sub>1) = exec (WHILE b DO d) s\<^sub>2 (min f\<^sub>1 f\<^sub>2)" by simp 
    from this first_cond exec_fuel_nonincreasing have
     pre2: "exec (WHILE b DO d) s\<^sub>1 (Suc f\<^sub>1) = exec (WHILE b DO d) s\<^sub>2 f\<^sub>2" 
      using min_absorb2 by force
    show ?thesis 
      by (metis Pair_inject WhileTrue.prems inst1 less_le_trans pre2 second_cond)
  qed
qed auto+

theorem bigstep_imp_exec: "(c,s) \<Rightarrow> s' \<Longrightarrow> \<exists>f f'. f' > 0 \<and> exec c s f = (s', f')"
  by (simp add: bigstep_imp_exec_aux)

corollary exec_equiv_bigstep: "(\<exists>f f'. exec c s f = (s', f') \<and> f' > 0) \<longleftrightarrow> (c,s) \<Rightarrow> s'"
  by (metis bigstep_imp_exec exec_imp_bigstep)

end