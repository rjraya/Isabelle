theory Ex12Comp
imports Compiler
begin

value "ccomp (IF Less (V ''x'') (N 5) THEN ''y'' ::= N 3 ELSE SKIP)"

(* jmp implicit plus one since it is always skipped *)
fun ccomp_opt :: "com \<Rightarrow> instr list" where
"ccomp_opt SKIP = []" |
"ccomp_opt  (x ::= a) = acomp  a @ [STORE x]" |
"ccomp_opt  (c\<^sub>1;;c\<^sub>2) = ccomp_opt  c\<^sub>1 @ ccomp_opt  c\<^sub>2" |
"ccomp_opt  (IF b THEN c\<^sub>1 ELSE SKIP) =
  (let cc\<^sub>1 = ccomp_opt  c\<^sub>1; cb = bcomp b False (size cc\<^sub>1) 
   in cb @ cc\<^sub>1)" |
"ccomp_opt  (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp_opt  c\<^sub>1; cc\<^sub>2 = ccomp_opt  c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp_opt  (WHILE b DO c) =
 (let cc = ccomp_opt  c; cb = bcomp b False (size cc + 1)
  in cb @ cc @ [JMP (-(size cb + size cc + 1))])"

lemma ccomp_opt_if:
  assumes "c\<^sub>2 \<noteq> SKIP"
  shows
  "ccomp_opt (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp_opt c\<^sub>1; cc\<^sub>2 = ccomp_opt c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)"
  using assms by (cases c\<^sub>2) auto

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp_opt c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp_opt c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def intro!: acomp_correct cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp_opt c1"  let ?cc2 = "ccomp_opt c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  also
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce
  finally show ?case by simp
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp_opt c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp_opt(WHILE b DO c)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb,s1,stk)"
    using \<open>bval b s1\<close> by (fastforce intro!: bcomp_correct)
  moreover
  have "?cw \<turnstile> (size ?cb,s1,stk) \<rightarrow>* (size ?cb + size ?cc,s2,stk)"
    using WhileTrue.IH(1) by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
next
  case (IfFalse b s c2 t c1) 
  let ?cc1 = "ccomp_opt c1"
  let ?cc2 = "ccomp_opt c2"
  show ?case
  proof(cases "c2 = SKIP")
    case True
    let ?cb = "bcomp b False (size ?cc1)"
    from True show ?thesis using IfFalse(1-2) 
      using bcomp_correct[of "size ?cc1" b False s stk] by auto
  next
    case False 
    let ?cb = "bcomp b False (size ?cc1 + 1)"
    from ccomp_opt_if[of c2 b c1] False
    have "ccomp_opt (IF b THEN c1 ELSE c2) =
          ?cb @ ?cc1 @ (JMP (size ?cc2) # ?cc2)" by simp
    from this  show ?thesis using IfFalse(1) IfFalse(3) 
      using bcomp_correct[of "size ?cc1 + 1" b False s stk] by force
  qed  
next
  case (IfTrue b s c1 t c2) 
  let ?cc1 = "ccomp_opt c1"
  let ?cc2 = "ccomp_opt c2"
  show ?case
  proof(cases "c2 = SKIP")
    case True
    let ?cb = "bcomp b False (size ?cc1)"
    from True show ?thesis using IfTrue(1) IfTrue(3)
      using bcomp_correct[of "size ?cc1" b False s stk] by force
  next
    case False 
    let ?cb = "bcomp b False (size ?cc1 + 1)"
    from ccomp_opt_if[of c2 b c1] False
    have "ccomp_opt (IF b THEN c1 ELSE c2) =
          ?cb @ ?cc1 @ (JMP (size ?cc2) # ?cc2)" by simp
    from this show ?thesis using IfTrue
      using bcomp_correct[of "size ?cc1 + 1" b False s stk] 
      sorry
  qed  
qed (fastforce intro!: bcomp_correct)+


end