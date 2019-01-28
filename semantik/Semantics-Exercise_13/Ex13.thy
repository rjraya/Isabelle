theory Ex13
  imports "IMP.Small_Step" "IMP.Def_Init"
begin

(*an example of mutually recursive equations*)
fun ev and odd where
 "ev 0 = True" |
 "ev (Suc n) = odd n" |
 "odd 0 = False" |
 "odd (Suc n) = ev n"

fun AA :: "com \<Rightarrow> (vname \<times> aexp) set \<Rightarrow> (vname \<times> aexp) set" where
 "AA SKIP A = A" |
 "AA (x::=a) A = (if x \<in> vars a then {} else {(x,a)}) 
                 \<union> {(x',a'). (x',a') \<in> A \<and> x \<notin> {x'} \<union> vars a'}" |
 "AA (c1;;c2) A = (AA c2 (AA c1 A))" |
 "AA (IF b THEN c1 ELSE c2) A = AA c1 A \<inter> AA c2 A" |
 "AA (WHILE b DO c) A = A \<inter> AA c A"

fun gen and kill :: "com \<Rightarrow> (vname \<times> aexp) set"  where
"gen SKIP = {}" |
"kill SKIP = {}" |
"gen (x::=a) = (if x \<in> vars a then {} else {(x,a)})" |
"kill (x::=a) = {(x',a'). x = x' \<and> a \<noteq> a' \<or> x \<in> vars a'}" |
"gen (c1;;c2) = (gen c1 - kill c1)  \<union> gen c2" |
"kill (c1;;c2) = (kill c1 - gen c2) \<union> kill c2" |
"gen (IF b THEN c1 ELSE c2) = gen c1 \<inter> gen c2" |
"kill (IF b THEN c1 ELSE c2) = kill c1 \<union> kill c2" |
"gen (WHILE b DO c) = {}" |
"kill (WHILE b DO c) = kill c" 

lemma AA_gen_kill: "AA c A = (A \<union> gen c) - kill c"
  apply(induction c arbitrary: A)
  apply auto
  done

(* the analysis is idempotent *)
lemma AA_idemp: "AA c (AA c A) = AA c A" by (auto simp: AA_gen_kill)

lemma AA_sound_aux:
  assumes "(c,s) \<Rightarrow> s'" "\<forall> (x,a) \<in> A. s x = aval a s"
  shows "\<forall> (x,a) \<in> AA c A. s' x = aval a s'"
  using assms
proof(induction arbitrary: A rule: big_step_induct)
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3) then show ?case by fastforce
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue.IH(1) WhileTrue.prems have "\<forall> (x,a) \<in> AA c A. s\<^sub>2 x = aval a s\<^sub>2" .
  from WhileTrue.IH(2)[OF this] have "\<forall> (x,a) \<in> AA (WHILE b DO c) (AA c A). s\<^sub>3 x = aval a s\<^sub>3" .
  then show ?case 
    apply(simp)
    apply(subst (asm) AA_idemp)
    apply simp (* review this! *)
    done
qed auto

theorem AA_sound: 
 "(c,s) \<Rightarrow> s' \<Longrightarrow> \<forall> (x,a) \<in> AA c {}. s' x = aval a s'"
  by(rule AA_sound_aux,assumption,simp)
 
end


