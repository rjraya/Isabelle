section "Small-Step Semantics of Commands"

theory Small_Step imports Big_Step begin

thm not_distinct_decomp
thm length_induct

find_theorems finite name: "induct"



subsection "The transition relation"

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"


abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y \<equiv> (small_step\<^sup>*\<^sup>* x y)"

(* rtranclp -- reflexive transitive closure (for predicate) *)

term rtranclp
term "rtranclp R"

(* ctrl-e <up> *   *)



subsection\<open>Proof infrastructure\<close>

subsubsection\<open>Induction rules\<close>

text\<open>The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form @{text"a \<rightarrow> b \<Longrightarrow> \<dots>"} where @{text a} and @{text b} are
not already pairs @{text"(DUMMY,DUMMY)"}. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
@{text"\<rightarrow>"} into pairs:\<close>
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection\<open>Proof automation\<close>

declare small_step.intros[simp,intro]

text\<open>Rule inversion:\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
thm WhileE

text\<open>A simple property:\<close>
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done

lemma deterministic':
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
proof(induction arbitrary: cs'' rule: small_step.induct)
  case (Seq1 c\<^sub>2 s)
  from Seq1.prems have "cs'' = (c\<^sub>2,s)"
  proof cases
    case Seq1
    then show ?thesis .
  next
    case (Seq2 c\<^sub>1' s')
    from Seq2(2) have False by cases
    then show ?thesis ..
  qed
qed blast+



subsection "Equivalence with big-step semantics"

(* Appending steps *)
thm rtranclp_induct2

thm rtranclp.rtrancl_refl
thm rtranclp.rtrancl_into_rtrancl

(* Prepending steps *)
thm converse_rtranclp_induct2

thm rtranclp.rtrancl_refl
thm converse_rtrancl_into_rtrancl


(** \<dots> need some shorter names *)

(* Prepending steps *)
lemmas star_induct = converse_rtranclp_induct2 (* Pairs *)
lemmas star_induct1 = converse_rtranclp_induct (* No pairs *)

lemmas star_refl = rtranclp.rtrancl_refl
lemmas star_step = converse_rtranclp_into_rtranclp

lemmas star_step1 = r_into_rtranclp

lemmas star_trans = rtranclp_trans

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case (step c1 s1 ch sh)
  
  from Seq2[OF step.hyps(1)] have "(c1;; c2, s1) \<rightarrow> (ch;; c2, sh)" .
  also have \<open>\<dots> \<rightarrow>* (c1';; c2, s')\<close> by (rule step.IH)
  finally show ?case .
qed

lemma seq_comp':
  assumes 1: "(c1,s1) \<rightarrow>* (SKIP,s2)"
  assumes 2: "(c2,s2) \<rightarrow>* (SKIP,s3)"
  shows "(c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
proof -
  note star_seq2[OF 1] also note Seq1 also note 2 finally show ?thesis .
qed  
  


lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
by(blast intro: star_step star_seq2 star_trans)

text\<open>The following proof corresponds to one on the board where one would
show chains of @{text "\<rightarrow>"} and @{text "\<rightarrow>*"} steps.\<close>

lemma r_r_rtrancl: "r x y \<Longrightarrow> r y z \<Longrightarrow> r\<^sup>*\<^sup>* x z" by simp


lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP,s) \<rightarrow>* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  thm big_step.Seq

  fix c1 c2 s1 s2 s3
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  thus "(c1;;c2, s1) \<rightarrow>* (SKIP,s3)" by (rule seq_comp)
next
  thm big_step.IfTrue
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c0,s)" by (rule IfTrue)
  also assume "(c0,s) \<rightarrow>* (SKIP,t)"
  finally 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" .
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c1,s)" by simp
  moreover assume "(c1,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star_step)
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c;; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if,s) \<rightarrow> (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)" by(metis star_refl star_step)
next
  thm big_step.WhileTrue
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
  assume c: "(c,s) \<rightarrow>* (SKIP,s')"
  assume b: "bval b s"
  
  note [trans] = r_r_rtrancl[of "small_step"] (* explicit instantiation required, 
    otherwise Isabelle's unifier get's 'creative' in finding instance for ?r *)
  
  have "(?w,s) \<rightarrow> (?if, s)" by (rule While)
  also have "(?if, s) \<rightarrow> (c;; ?w, s)" using b by (rule IfTrue)
  also have "(c;; ?w,s) \<rightarrow>* (SKIP,t)" by(rule seq_comp[OF c w])
  finally show "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)" .
qed

text\<open>Each case of the induction can be proved automatically:\<close>
lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star_step)
next
  case IfFalse thus ?case by (blast intro: star_step)
next
  case WhileFalse thus ?case
    by (metis star_step star_refl small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by(metis While seq_comp small_step.IfTrue star_step[of small_step])
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction cs rule: star_induct1)
apply (auto intro: small1_big_continue)
done

text \<open>
  Finally, the equivalence theorem:
\<close>
theorem big_iff_small:
  "cs \<Rightarrow> t \<longleftrightarrow> cs \<rightarrow>* (SKIP,t)"
by(metis big_to_small small_to_big)


subsection "Final configurations and infinite reductions"

definition "final cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP"
apply(simp add: final_def)
apply(induction c)
apply blast+
done

lemma final_iff_SKIP: "final (c,s) = (c = SKIP)"
by (metis SkipE finalD final_def)

text\<open>Now we can show that @{text"\<Rightarrow>"} yields a final state iff @{text"\<rightarrow>"}
terminates:\<close>

lemma big_iff_small_termination:
  "(\<exists>t. cs \<Rightarrow> t) \<longleftrightarrow> (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
by(simp add: big_iff_small final_iff_SKIP)

text\<open>This is the same as saying that the absence of a big step result is
equivalent with absence of a terminating small step sequence, i.e.\ with
nontermination.  Since @{text"\<rightarrow>"} is determininistic, there is no difference
between may and must terminate.\<close>

end
