theory tut07
imports "IMP2.VCG"
begin
declare [[names_short]]

text \<open>\ExerciseSheet{7}{27.11.2018}\<close>

text \<open>\Exercise{While Invariants}\<close>
partial_function (option) while where
  "while b f s = (if b s then while b f (f s) else Some s)"
  
lemmas while_unfold = while.simps

text \<open>
We have pre-defined a while-combinator
\begin{center}
@{term while} :: @{typ "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option"}
\end{center}
such that the following unfolding property holds:
\begin{center}
@{thm  while_unfold[no_vars]}
\end{center}\<close>

text \<open>To prove anything about the computation result of \<open>while\<close> we need to use a proof rule
with an invariant (similarly to what you have seen for the weakest precondition calculus).
Prove that the following rule is correct:
\<close>
theorem while_invariant:
  assumes "wf R" and "I s"
    and "\<And>s. I s \<Longrightarrow> b s \<Longrightarrow> I (f s) \<and> (f s, s) \<in> R"
  shows "\<exists>s'. I s' \<and> \<not> b s' \<and> while b f s = Some s'"
  using assms(1,2)
proof induction
  case (less s)
  then show ?case by (simp add: assms(3) while_unfold)
qed
 (* proof(cases "b s") (* case distinction, loop terminates or not *)
    case True
    from assms(3)[OF \<open>I s\<close> \<open>b s\<close>] have "(f s, s) \<in> R" "I (f s)" by auto  
    from less.IH[OF this] obtain s' where "I s'"  "\<not> b s'" " while b f s = Some s'" by auto
    using \<open>b s\<close> by (simp add: while_unfold)
     
    then show ?thesis sorry
next
  case False
  with less have "I s" "\<not> b s" " while b f s = Some s" by(auto simp: while_unfold)
  then show ?thesis by blast
qed*)
  

text \<open>Here is an example of how we can use this rule:\<close>
definition
  "list_sum xs \<equiv> fst (the (while (\<lambda>(s, xs). xs \<noteq> []) (\<lambda>(s, xs). (s + hd xs, tl xs)) (0, xs)))"

lemma list_sum_list_sum:
  "list_sum xs = sum_list xs"
proof -
  let ?I = "\<lambda>(s,ys). sum_list xs = s + sum_list ys \<and> length ys \<le> length xs"

  let ?R = "{((s, as), (s', bs)). length as < length bs \<and> length bs \<le> length xs}"
  have "wf ?R"
    by (rule wf_bounded_measure[where
          ub = "\<lambda>_. length xs" and f = "\<lambda>(_, ys). length xs - length ys"]) auto
  have "\<exists> s'. ?I s' \<and> \<not> (\<lambda>(s, xs). xs \<noteq> []) s' \<and>
    while (\<lambda>(s, xs). xs \<noteq> []) (\<lambda>(s, xs). (s + hd xs, tl xs)) (0, xs) = Some s'"
    apply (rule while_invariant[OF \<open>wf ?R\<close>])
    apply auto
    subgoal for zs ys
    by(cases ys; simp add: algebra_simps)
  done
  then show ?thesis
    unfolding list_sum_def by auto
qed
text \<open>Fill in a suitable invariant!\<close>

text \<open>
  \Exercise{Weakest Preconditions}
\<close>
text \<open>You have seen this definition of sum of the first \<open>n\<close> natural numbers before:\<close>
fun sum :: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + i)"

lemma sum_simps[simp]:
  "0 < i \<Longrightarrow> sum i = sum (i - 1) + i"
  "i \<le> 0 \<Longrightarrow> sum i = 0"
  by simp+

lemmas [simp del] = sum.simps

text \<open>
  Consider the following program to calculate the sum of the first \<open>n\<close> natural numbers.
  Find suitable variants and invariants and prove that it fulfills the specification!
\<close>
program_spec sum_prog
  assumes "n \<ge> 0" ensures "s = sum n\<^sub>0"
  defines \<open>
    s = 0;
    i = 0;
    while (i < n)
      @variant \<open>nat (n - i)\<close> 
      @invariant \<open>s = sum i \<and> s \<ge> 0 \<and> i \<ge> 0 \<and> n = n\<^sub>0 \<and> i \<le> n :: bool\<close>
    {
      i = i + 1;
      s = s + i
    }
  \<close>
  apply vcg by auto
  (* i \<le> n because the invariant has to hold in the last iteration of the loop *)
  (*
   apply vcg_cs (* vcg with some clarsimps at the end *)
   try to exchange the order of the two statements in the while loop
   we will have to do a case distiction with the start and the end of the loop
   this can be done with an if statement in the invariant
  *)

text \<open>Recall the following scheme for squaring a non-negative integer:
\begin{verbatim}
  1 2 3 4
  2 2 3 4
  3 3 3 4
  4 4 4 4
\end{verbatim}
\<close>
text \<open>Write down a program that implements this algorithm following the ``count up scheme''
and prove that it is correct!
\<close>

program_spec square_prog
  assumes "n \<ge> 0" ensures "s = n\<^sub>0*n\<^sub>0"
  defines \<open>
    s = 0;
    i = 0;
    while (i < n)
      @variant \<open>nat (n-i)\<close> 
      @invariant \<open>n \<ge> 0 \<and> s = i*i \<and> i \<le> n \<and> 0 \<le> i \<and> n = n\<^sub>0 :: bool\<close>
    {
      s = s + (2*i+1);
      i = i + 1
    }
  \<close>
  apply vcg 
  apply(auto simp: algebra_simps)
  done

end