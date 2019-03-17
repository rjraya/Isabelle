theory Submission
  imports Defs
begin

(* Exercise 1 *)

datatype paren = Open | Close

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] _ = 0" |
"count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"

inductive S where
  S_empty: "S []" |
  S_append: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (xs @ ys)" |
  S_paren: "S xs \<Longrightarrow> S (Open # xs @ [Close])"

inductive T where
  T_empty: "T []" |
  T_append: "T xs \<Longrightarrow> T ys \<Longrightarrow> T (xs @ ys)" |
  T_paren: "T xs \<Longrightarrow> T (Open # xs @ [Close])" |
  T_left: "T xs \<Longrightarrow> T (Open # xs)"

theorem S_T: "S xs \<Longrightarrow> T xs"
  apply(induction rule: S.induct)
  apply(auto intro: T.intros)
done

lemma count_append: "count (xs @ ys) v = (count xs v) + (count ys v)"
  apply(induction xs)
  apply(auto)
done

lemma T_count: "T xs \<Longrightarrow> count xs Close \<le> count xs Open" 
  apply(induction rule: T.induct) 
  apply simp
  apply(auto simp: T.intros count_append)
  done

lemma T_S: "T xs \<Longrightarrow> count xs Open = count xs Close \<Longrightarrow> S xs"
  apply(induction rule: T.induct)
  apply(auto simp add: S.intros count_append)
  apply (metis S_append T_count add.commute le_less less_add_eq_less not_le)
  using T_count by fastforce

(* Exercise 2 *)

type_synonym reg = nat

datatype op = REG reg | VAL int \<comment> \<open>An operand is either a register or a constant.\<close>

datatype instr =
  LD reg vname \<comment> \<open>Load a variable value in a register.\<close>
| ADD reg op op \<comment> \<open>Add the contents of the two operands, placing the result in the register.\<close>

datatype v_or_reg = Var vname | Reg reg
type_synonym mstate = "v_or_reg \<Rightarrow> int"

fun op_val :: "op \<Rightarrow> mstate \<Rightarrow> int" where
  "op_val (REG r) \<sigma> = \<sigma> (Reg r)" |
  "op_val (VAL n) _ = n"

fun exec :: "instr \<Rightarrow> mstate \<Rightarrow> mstate" where
  "exec (LD r vn) \<sigma> = \<sigma>(Reg r := \<sigma> (Var vn))" |
  "exec (ADD r o1 o2) \<sigma> = \<sigma>(Reg r := (op_val o1 \<sigma>) + (op_val o2 \<sigma>))"

fun execs :: "instr list \<Rightarrow> mstate \<Rightarrow> mstate" where
  "execs [] \<sigma> = \<sigma>" |
  "execs (i#is) \<sigma> = execs is (exec i \<sigma>)"

fun cmp :: "aexp \<Rightarrow> reg \<Rightarrow> op \<times> instr list" where
  "cmp (N n) r = (VAL n,[])" |
  "cmp (V x) r = (REG r,[LD r x])" |
  "cmp (Plus a a1) r = 
    (REG r,(let (op1,il1) = (cmp a r) in
             (let  (op2,il2) = (cmp a1 (r+1))  in 
              il1 @ il2 @ [ADD r op1 op2]
      ))
    )"

value "aval (Plus (V ''a'') (N 1)) <>"
value "cmp (Plus (V ''a'') (N 1)) (1::nat)"


(* Execs commutes with list concatenation *)
lemma execs_concat: "execs (il1 @ il2) ms = execs il2 (execs il1 ms)" 
  apply(induction il1 arbitrary: ms)
  apply(auto)
done

(* If we compile to some register then this register is the one we indicated *)
lemma compiled_reg[simp]: "(cmp a r) = (REG r',p)  \<Longrightarrow> r = r'"
apply(induction a)
apply(auto split: prod.splits)
done

(* The instructions produced do not alter registers below r *)
lemma instr_below[simp]: "r' < r \<Longrightarrow> (cmp a r) = (x,p) \<Longrightarrow> (execs p ms)(Reg r') = ms(Reg r') "
  apply(induction a r arbitrary: ms p r' x rule: cmp.induct)
  apply(auto simp: execs_concat  split: prod.splits)
done

(* Updating a register, does not affect the variables *)
lemma update_reg[simp]: "\<sigma> (Reg r := x) o Var = \<sigma> o Var" by auto

(* Execution of instructions does not affect the variable state *)
lemma instr_var_state[simp]: "(exec i \<sigma>) o Var = \<sigma> o Var" by (metis exec.elims update_reg)

lemma instrl_var_state[simp]: "(execs il \<sigma>) o Var = \<sigma> o Var"
  apply(induction il arbitrary: \<sigma>)
  apply(auto)
done

theorem cmp_correct: "cmp a r = (x, prog) \<Longrightarrow>
  op_val x (execs prog \<sigma>) = aval a (\<sigma> o Var) \<and> execs prog \<sigma> o Var = \<sigma> o Var"
\<comment> \<open>The first conjunct states that the resulting operand contains the correct value,
    and the second conjunct states that the variable state is unchanged.\<close>
  apply(induction a arbitrary: x prog \<sigma> r )
  apply(auto simp: execs_concat split: prod.splits)
  apply(metis compiled_reg instr_below lessI op.distinct(1) op.inject(2) op_val.elims)
done

(* Exercise 3 *)

definition "ex_split P xs \<longleftrightarrow> (\<exists>ys zs. xs = ys @ zs \<and> P ys zs)"

fun has_split :: "('a list \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "has_split P [] [] = P [] []" |
  "has_split P ys [] = P ys []" |
  "has_split P [] (x#xs) \<longleftrightarrow> (P [] (x#xs)) \<or> (has_split P [x] xs)" |
  "has_split P ys (x#xs) \<longleftrightarrow> (P ys (x#xs)) \<or> (has_split P (ys@[x]) xs)"

lemma hs_imp1: "has_split P ts xs \<Longrightarrow> \<exists> ys zs. xs = ys @ zs \<and> P (ts @ ys) zs"
  apply(induction P ts xs rule: has_split.induct)
  apply(simp)
  apply(simp)
  apply(cases) 
  apply(simp)
  apply(force)
  apply(cases)
  apply(force)
  apply(force)
done

lemma hs_imp2_aux: "P ys zs \<Longrightarrow>  has_split P ys zs"
  apply(induction P ys zs rule: has_split.induct)
  apply(auto) 
done

lemma hs_imp2: "\<exists> ys zs. xs = ys @ zs \<and> P (ts @ ys) zs \<Longrightarrow> has_split P ts xs"
  apply(induction P ts xs rule: has_split.induct)
  apply(auto simp: hs_imp2_aux Cons_eq_append_conv)
done

lemmas part1 = hs_imp1 [where ts = "[]" ]
lemmas part2 = hs_imp2 [where ts = "[]" ]

theorem ex_split_has_split[code]: "ex_split P xs \<longleftrightarrow> has_split P [] xs"
  apply(rule iffI[rotated])
  apply(auto simp: ex_split_def part2)
  using part1 apply auto
done
 
definition
  "ex_balanced_sum xs = (\<exists> ys zs. sum_list ys = sum_list zs \<and> xs = ys @ zs \<and> ys \<noteq> [] \<and> zs \<noteq> [])"

definition P where
"P xs ys \<longleftrightarrow> xs \<noteq> [] \<and> ys \<noteq> [] \<and> sum_list xs = sum_list ys"

theorem ex_balance_sum [code]: "ex_balanced_sum xs \<longleftrightarrow> ex_split P xs"
  apply(auto simp: ex_balanced_sum_def ex_split_def P_def)
done
  
value "ex_balanced_sum [1,2,3,3,2,1::nat]"

(* Exercise 4 *)


fun linear_split :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "linear_split [] s1 s2 = False" |
  "linear_split [x] s1 s2 = False" |
  "linear_split (x # y # xs) s1 s2 = ((s1 - x = s2 + x) \<or> linear_split (y # xs) (s1 - x) (s2 + x))"

lemma concat_linear_split[simp]: "linear_split (x # y # xs) (sum_list (x # y # xs)) 0 \<Longrightarrow> 
           linear_split ((x + y) # xs) (sum_list ((x + y) # xs)) 0 \<or> x = sum_list (y # xs)"
  apply(induction xs arbitrary: x y)
  apply(auto)
done

lemma linear_correct_1: "linear_split xs (sum_list xs) 0 \<Longrightarrow> ex_balanced_sum xs"
proof(induction xs rule: length_induct)
  case (1 xs) show ?case
  proof-
    from "1.prems" obtain x y ls where split_form: 
      "xs = x # y # ls" by (meson linear_split.elims(2))

    (* Rewriting on linear split gives two cases *)
    from this "1.prems" concat_linear_split have split_cases:
      "linear_split ((x + y) # ls) (sum_list ((x + y) # ls)) 0 \<or> x = sum_list (y # ls)" by blast

    (* First case is solved automatically *)
    have first_case: "x = sum_list (y # ls) \<Longrightarrow> ex_balanced_sum xs" 
      by (metis append.left_neutral append_Cons append_Nil2 ex_balanced_sum_def 
          list.distinct(1) split_form sum_list.Cons sum_list.append)

    {
      (* Second case requires the strong induction on the length of the list *)
      assume "linear_split ((x + y) # ls) (sum_list ((x + y) # ls)) 0"
      from this "1.IH" split_form have "ex_balanced_sum ((x + y) # ls)" by simp
      from this ex_balanced_sum_def obtain ms ns where mn_concat:
        "(x + y) # ls = ms @ ns \<and> sum_list ms = sum_list ns \<and> ms \<noteq> [] \<and> ns \<noteq> []" by blast
      from this obtain ts where "ms = (x + y) # ts" by(metis append_eq_Cons_conv)
      from this mn_concat split_form have
        "sum_list (x # y # ts) = sum_list ns \<and> xs = (x # y # ts) @ ns \<and>  
          (x # y # ts) \<noteq> [] \<and> ns \<noteq> []" by auto
      from this ex_balanced_sum_def have "ex_balanced_sum xs" by blast
    }
    from this first_case split_cases show ?thesis by blast
  qed
qed

lemma sum_linear_split: 
  "linear_split ((x + y) # ls) (sum_list ((x + y) # ls)) 0  \<Longrightarrow> 
   linear_split (x # y # ls) (sum_list (x # y # ls)) 0"
  apply(smt list.sel(3) linear_split.elims(2) linear_split.simps(3) sum_list.Cons)
done

lemma linear_correct_2: "ex_balanced_sum xs \<Longrightarrow> linear_split xs (sum_list xs) 0"
proof(induction xs rule: length_induct)
  case (1 xs) show ?case
  proof -
    from "1.prems" ex_balanced_sum_def obtain ys zs where concat:
      "sum_list ys = sum_list zs \<and> xs = ys @ zs \<and> ys \<noteq> [] \<and> zs \<noteq> []" by blast

    (* There are two possibilities for ys based on concat*)
    have ys_cases: "\<exists> x y xs. ys = x # y # xs \<or> (\<exists> x. ys = [x])" by (metis hd_Cons_tl concat)

    (* First case is easy *)
    from concat linear_split.elims(3) have 
      first_case: "\<exists> x. ys = [x] \<Longrightarrow> linear_split xs (sum_list xs) 0" by fastforce
    
    {
      (* Second case requires the strong induction on the length of the list *)
      assume "\<exists>x y xs. ys = x # y # xs"
      from this obtain x y ls where ys_concat: "ys = x # y # ls" by auto 
      from this concat have 
        "sum_list ((x + y) # ls) = sum_list zs \<and> ((x + y) # ls) \<noteq> [] \<and> zs \<noteq> []" by auto
      from this ex_balanced_sum_def "1.IH" concat ys_concat have 
        "linear_split (((x + y) # ls) @ zs) (sum_list (((x + y) # ls) @ zs)) 0" 
      by (metis add.right_neutral add_Suc_right add_mono_thms_linordered_field(1) 
          length_append lessI list.size(4))
      from this sum_linear_split concat ys_concat have 
        "linear_split xs (sum_list xs) 0" by (metis append_Cons)
    }
      from this first_case  ys_cases show ?case by(auto)
  qed  
qed

lemma linear_correct: "ex_balanced_sum xs \<longleftrightarrow> linear_split xs (sum_list xs) 0"
  apply(rule iffI[rotated]) 
  apply(auto simp add: linear_correct_1)
  apply(auto simp add: linear_correct_2)
done

end