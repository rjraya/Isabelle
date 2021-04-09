theory Defs
  imports "IMP2.Examples"
begin

lemma [named_ss vcg_bb]:
  "lhsv (Inline c) = lhsv c"
  unfolding Inline_def ..

lemma lran_split:
  "lran a l h = lran a l p @ lran a p h" if "l \<le> p" "p \<le> h"
  using that by (induction p; simp; simp add: lran.simps)

lemma lran_eq_iff':
  "lran a l h = as @ bs \<longleftrightarrow> (\<exists> i. l \<le> i \<and> i \<le> h \<and> as = lran a l i \<and> bs = lran a i h)" if "l \<le> h"
  apply safe
  subgoal
    using that
  proof (induction as arbitrary: l)
    case Nil
    then show ?case
      by auto
  next
    case (Cons x as)
    from this(2-) have "lran a (l + 1) h = as @ bs" "a l = x" "l + 1 \<le> h"
        apply -
      subgoal
        by simp
      subgoal
        by (smt append_Cons list.inject lran.simps lran_append1)
      subgoal
        using add1_zle_eq by fastforce
      done
    from Cons.IH[OF this(1,3)] guess i by safe
    note IH = this
    with \<open>a l = x\<close> show ?case
      apply (intro exI[where x = i])
      apply auto
      by (smt IH(3) lran_prepend1)
  qed
  apply (subst lran_split; simp)
  done

end