theory Submission
  imports Defs
begin

(* This theorem comes from the exercise session *)
theorem path_is_path:
  "path E u xs v \<longleftrightarrow> is_path E u xs v"
proof (induction xs arbitrary: u)
  case Nil
  then show ?case
    by (auto simp: path_Nil)
next
  case (Cons x xs)
  then show ?case
    by (cases xs) (auto simp: path_Nil path_Cons)
qed

(* Path composition operation *)
lemma path_append: 
      "is_path E u p1 y \<Longrightarrow>
       is_path E y p2 v \<Longrightarrow>
       is_path E u (p1 @ p2) v"
proof(induction rule: is_path.induct)
  case (NilI u)
  then show ?case by auto
next
  case (ConsI u v l w)
  then show ?case using is_path.ConsI by fastforce  
qed

(* Break path into short subpaths *)
lemma path_break_fun:
     "path E u (xs @ [y] @ zs) v \<Longrightarrow>
      path E u xs y \<and> path E y (y # zs) v"
proof -
  assume assms: "path E u (xs @ [y] @ zs) v"
  then show "path E u xs y \<and> path E y (y # zs) v"
  proof(induction E u xs y arbitrary: zs rule: path.induct)
    case (1 E u v)
    then show ?case 
      by (metis Cons_eq_appendI append_Nil list.collapse path.simps(1) path.simps(2) path.simps(3))
  next
    case (2 E u v w)
    then show ?case by auto 
  next
    case (3 E u x y xs v)
    then show ?case by auto 
  qed
qed

lemma path_break:
     "is_path E u (xs @ [y] @ zs) v \<Longrightarrow>
      is_path E u xs y \<and> path E y (y # zs) v"
  by (meson path_break_fun path_is_path)

(* This lemma will assist us in the proof for the given list *)
lemma shorten_lemma:
     "is_path E u (xs @ [y] @ ys @ [y] @ zs) v  \<Longrightarrow>
       is_path E u (xs @ [y] @ zs) v"
  by (metis append.left_neutral append_Cons path_append path_break path_is_path)

theorem path_distinct:
  assumes "is_path E u p v"
  shows "\<exists>p'. distinct p' \<and> is_path E u p' v"
  using assms
proof (induction p rule: length_induct)
  case step: (1 p)
  note IH = step.IH
  note prems = step.prems
  show ?case proof (cases "distinct p")
    case True then show ?thesis using prems by auto
  next
    case False
    from this not_distinct_decomp  obtain xs ys zs y where 
     list_form: "p = xs @ [y] @ ys @ [y] @ zs" by blast
    from this prems shorten_lemma have 
     short_path: "is_path E u (xs @ [y] @ zs) v" by auto
    from IH have
      "length (xs @ [y] @ zs) < length p \<longrightarrow>
         is_path E u (xs @ [y] @ zs) v \<longrightarrow> 
         (\<exists>p'. distinct p' \<and> is_path E u p' v)" by blast         
    from this list_form short_path  show ?thesis by auto     
  qed
qed

end