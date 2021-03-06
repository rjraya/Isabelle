theory Exam
  imports Main 
   "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/Com"
   "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/Big_Step"
   "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/vars"

begin 

inductive p where
 "p []" 
| "p [x]"
| "p xs \<Longrightarrow> p ([x] @ xs @ [x])"

term rev

lemma rev_app: "rev (xs @ ys) = rev ys @ rev xs"
  by(induction xs,auto)

lemma "xs @ (ys @ zs) = (xs @ ys) @ zs"
  by(induction xs,auto)
  

lemma "p xs \<Longrightarrow> rev xs = xs"
  by(induction rule: p.induct,auto)

lemma my_induct: "P [] \<Longrightarrow> (\<And> x. P [x]) \<Longrightarrow> 
       (\<And> x y xs. P xs \<longrightarrow> P ([x] @ xs @ [y])) \<Longrightarrow> P xs"
  sorry

lemma l1: "[y] @ l = [x] @ l' \<Longrightarrow> y = x" by simp

lemma l2: "l1 @ xs @ l2 = l1 @ ys @ l2 \<Longrightarrow> xs = ys" by simp


lemma "rev xs = xs \<Longrightarrow> p xs"
proof(induction rule: my_induct)
  case 1
  then show ?case using p.intros by simp
next
  case (2 x)
  then show ?case using p.intros(2) rev.simps(2) by fast
next
  case (3 x y xs)
  then show ?case
  proof((rule impI)+)
    assume 1: "rev xs = xs \<longrightarrow> p xs"
    assume 2: "rev ([x] @ xs @ [y]) = [x] @ xs @ [y]"
    have 3: "rev ([x] @ xs @ [y]) =
                 rev [y] @ rev xs @ rev [x]"  
      by simp
    from 3 have 4: "rev [y] @ rev xs @ rev [x] = [y] @ rev xs @ [x]"
      by simp
    from 2 3 4 have 5: "[y] @ rev xs @ [x] = [x] @ xs @ [y]"
      by argo
    thm l1 l2
    from 5 l1 have 6: "x = y" by fast
    from 5 6 l2 have "rev xs = xs" by auto
    from this 1 6 p.intros(3) show "p ([x] @ xs @ [y])" by fast    
  qed
qed

(*
fun s :: "com \<Rightarrow> bool" where
"s SKIP = True" |
"s (x ::= a) = False" |
"s (c1;;c2) = (s c1 \<and> s c2)" |
"s (IF b THEN c1 ELSE c2) = (s c1 \<and> s c2)" |
"s (WHILE b DO c) = False"

lemma seq_cong: "c1 \<sim> c11 \<Longrightarrow> c2 \<sim> c22 \<Longrightarrow> (c1 ;; c2) \<sim> (c11 ;; c22)"
  unfolding equiv_c_def
  by auto

lemma while_cong: 
  "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by (simp add: sim_while_cong)

lemma "s c \<Longrightarrow> c \<sim> SKIP"
proof(induction c)
  case (Seq c1 c2)
  then have "c1 \<sim> SKIP \<and> c2 \<sim> SKIP" by simp
  from this seq_cong have 1: "c1 ;; c2 \<sim> SKIP ;; SKIP" by simp
  have "SKIP ;; SKIP \<sim> SKIP" unfolding equiv_c_def by auto
  from this 1 equiv_trans
  show ?case by blast
next
  case (If b c1 c2)
  then have "c1 \<sim> SKIP \<and> c2 \<sim> SKIP" by auto
  then show ?case unfolding equiv_c_def by blast
qed auto
*)

lemma key: "(c,s) \<Rightarrow> t \<Longrightarrow>  vars b \<inter> lvars c = {} \<Longrightarrow> 
       bval b s = bval b t"
  apply(induction rule: big_step_induct)
  apply (auto simp add: bval_eq_if_eq_on_vars)
  done

lemma "
 vars b2 \<inter> lvars c1 = {} \<and> vars b2  \<inter> lvars c2 = {} \<Longrightarrow> 
 (c1,s) \<Rightarrow> t \<or> (c2,s) \<Rightarrow> t \<Longrightarrow>
 bval b2 s = bval b2 t
"
  using key by auto
  
lemma key2: "
 vars b2 \<inter> lvars c1 = {} \<and> vars b2  \<inter> lvars c2 = {} \<Longrightarrow>
 WHILE b1 DO IF b2 THEN c1 ELSE c2 \<sim>
 IF b2  THEN (WHILE b1 DO c1) ELSE (WHILE b1 DO c2)
" 
  unfolding equiv_c_def
proof(intro allI)
  fix s t
  assume 1: "vars b2 \<inter> lvars c1 = {} \<and> vars b2  \<inter> lvars c2 = {}"
  {have "(WHILE b1 DO IF b2 THEN c1 ELSE c2, s) \<Rightarrow> t \<Longrightarrow>
        (IF b2 THEN WHILE b1 DO c1 ELSE WHILE b1 DO c2, s) \<Rightarrow> t"
  proof(induction "WHILE b1 DO IF b2 THEN c1 ELSE c2" s t 
        arbitrary:  rule: big_step_induct)
    case (WhileFalse s)
    then show ?case by auto
  next
    case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
    then show ?case 
      using 1 key by auto 
  qed}
  note case1 = this
  {have "(IF b2 THEN WHILE b1 DO c1 ELSE WHILE b1 DO c2, s) \<Rightarrow> t \<Longrightarrow>
         (WHILE b1 DO IF b2 THEN c1 ELSE c2, s) \<Rightarrow> t 
       " 
 proof(induction "IF b2 THEN WHILE b1 DO c1 ELSE WHILE b1 DO c2" s t 
        arbitrary:  rule: big_step_induct)
   case (IfTrue s t)
   then show ?case  sorry
 next
   case (IfFalse s t)
   then show ?case  sorry
 qed}
  note case2 = this
  from case1 case2 show "(WHILE b1 DO IF b2 THEN c1 ELSE c2, s) \<Rightarrow> t =
           (IF b2 THEN WHILE b1 DO c1 ELSE WHILE b1 DO c2, s) \<Rightarrow> t"
    by blast
qed

  


  
end