theory Submission
  imports Defs
begin

datatype paren = Open | Close

inductive S where
  S_empty: "S []" |
  S_append: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (xs @ ys)" |
  S_paren: "S xs \<Longrightarrow> S (Open # xs @ [Close])"

inductive T where
  T_S: "T []" |
  T_append: "T xs \<Longrightarrow> T ys \<Longrightarrow> T (xs @ ys)" |
  T_paren: "T xs \<Longrightarrow> T (Open # xs @ [Close])" |
  T_left: "T xs \<Longrightarrow> T (Open # xs)"

theorem S_T:
  "S xs \<Longrightarrow> T xs"
  apply(induction rule: S.induct)
  apply(auto simp: T.intros)
done

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] _ = 0" |
"count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"

lemma count_append: "count (xs@ys) e = count xs e + count ys e"
  apply(induction xs)
   apply(auto)
  done

lemma count_T: "T xs \<Longrightarrow> count xs Open \<ge> count xs Close"
  apply(induction rule: T.induct)
  apply(auto simp: T.intros count_append)
  done

lemma count_TT: "T xs \<Longrightarrow> count xs Open = count xs Close \<Longrightarrow>
                 (xs = [] \<or> xs = (Open # ls @ [Close]) \<or> xs = ys @ zs)"
  apply(induction rule: T.induct)
     apply(force simp: T.intros)
  sorry


theorem T_S:
  "T xs \<Longrightarrow> count xs Open = count xs Close \<Longrightarrow> S xs"
  apply(induction rule: T.induct)
  apply(rule S_empty)
  
  sorry
  

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
  "execs (i#is) \<sigma> = (let \<sigma>1 = (exec i \<sigma>) in execs is \<sigma>1)"

fun cmp :: "aexp \<Rightarrow> reg \<Rightarrow> op \<times> instr list" where
  "cmp (N n) r = (VAL n,[])" |
  "cmp (V x) r = (REG r,[LD r x])" |
  "cmp (Plus a a1) r = 
    (let (op1,il1) = (cmp a r) in 
      (let (op2,il2) = (cmp a1 (r+1)) in
        (REG r,il1@il2@[ADD r op1 op2])
      )
    )"

(* Execs commutes with list concatenation *)
lemma execs_concat: "execs (il1 @ il2) ms = execs il2 (execs il1 ms)" 
  apply(induction il1 arbitrary: ms)
  apply(auto)
done

(* The instructions produced do not alter registers below r *)
lemma instr_below: "r' < r \<Longrightarrow> (execs (snd (cmp a r)) ms)(Reg r') = ms(Reg r') "
  apply(induction a r arbitrary: ms rule: cmp.induct)
  apply(auto simp: execs_concat split: prod.splits)
done

(* If we compile to some register then this is register is the one we indicated *)
lemma compiled_reg: "fst (cmp a r) = REG r' \<Longrightarrow> r = r'"
apply(induction a)
apply(auto split: prod.splits)
done

(* Updating a register, does not affect the variables *)
lemma update_reg: "s (Reg r := x) o Var = s o Var"
  by auto

theorem cmp_correct: "cmp a r = (x, prog) \<Longrightarrow>
  op_val x (execs prog \<sigma>) = aval a (\<sigma> o Var) \<and> execs prog \<sigma> o Var = \<sigma> o Var"
\<comment> \<open>The first conjunct states that the resulting operand contains the correct value,
    and the second conjunct states that the variable state is unchanged.\<close>
  apply(rule conjI)
  apply(induction prog \<sigma> rule: execs.induct)
  apply(induction a r  rule: cmp.induct)
      apply(auto simp: execs_concat split: prod.splits)
  sorry
  (*apply(auto simp : execs_concat instr_below)*)

  (*apply(simp add: update_reg compiled_reg instr_below execs_append)*)


definition "ex_split P xs \<longleftrightarrow> (\<exists>ys zs. xs = ys @ zs \<and> P ys zs)"

fun has_split :: "('a list \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "has_split P [] [] = P [] []" |
  "has_split P ys [] = P ys []" |
  "has_split P [] (x#xs) \<longleftrightarrow> (P [] (x#xs)) \<or> (has_split P [x] xs)" |
  "has_split P ys (x#xs) \<longleftrightarrow> (P ys (x#xs)) \<or> (has_split P (ys@[x]) xs)"


lemma l1: "P ys zs \<Longrightarrow>  has_split P ys zs"
  apply(induction P ys zs rule: has_split.induct)
  apply(auto) 
done
  
lemma l2: "has_split P ys zs \<Longrightarrow> has_split P [] (ys@zs)"
  apply(induction zs)
  apply(auto)
  sorry

lemma l3: "has_split P [] [x] \<longleftrightarrow> ex_split P [x]"
  apply(rule iffI)
  apply(simp add: ex_split_def)
  apply(blast)
  apply(simp add: ex_split_def)
  apply(rule exE)
  apply(auto)
  sorry


theorem ex_split_has_split[code]: "ex_split P xs \<longleftrightarrow> has_split P [] xs"
  apply(rule iffI[rotated])
  apply(auto simp: ex_split_def)
  apply(induction xs)
  apply(simp)
  sorry 

definition
  "ex_balanced_sum xs = (\<exists>ys zs. sum_list ys = sum_list zs \<and> xs = ys @ zs \<and> ys \<noteq> [] \<and> zs \<noteq> [])"

value "ex_balanced_sum [1,2,3,3,2,1::nat]"

definition
  "linear_split (xs :: int list) \<equiv> (undefined :: bool)"

theorem linear_correct:
  "linear_split xs \<longleftrightarrow> ex_balanced_sum xs"
  sorry

thm Suc_leD

end