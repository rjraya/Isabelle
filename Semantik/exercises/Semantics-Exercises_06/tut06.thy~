theory tut06
  imports IMP.Wp_Demo
begin

definition Max :: com where 
"Max = IF  (Less (V ''a'') (V ''b'')) THEN ''c'' ::= V ''b'' ELSE ''c'' ::= V ''a''"

lemma [simp]: "(a::int) < b \<Longrightarrow> max a b = b" by simp
  
lemma [simp]: "\<not>(a::int) < b \<Longrightarrow> max a b = a" by simp

lemma "wp Max (\<lambda>s'. s' ''c'' = max (s' ''a'') (s' ''b'')) s"
  unfolding Max_def
  by smartvcg (* unfolding wp_if_eq wp_assign_eq by simp *)
  (*apply(subst wp_if_eq)
  apply(simp split: if_split)
  apply(simp only: wp_assign_eq)
  apply(simp)*)
  
definition "MAX_wrong = (''a'' ::= N 0 ;;
                         ''b'' ::= N 0 ;;
                         ''c'' ::= N 0)"

lemma "wp MAX_wrong (\<lambda>s. s ''c'' = max (s ''a'') (s ''b'')) s"
  unfolding MAX_wrong_def
  by smartvcg
  (*
 unfolding MAX_wrong_def
 unfolding wp_seq_eq
 unfolding wp_assign_eq
 apply simp
 *)

lemma "a = s ''a'' \<and> b = s ''b'' \<Longrightarrow>
       wp Max (\<lambda>s. s ''c'' = max a b \<and> 
                   a = s ''a'' \<and> b = s ''b'') s"
  unfolding Max_def
  apply(subst wp_if_eq)
  apply(simp split: if_split)
  apply(simp only: wp_assign_eq)
  by auto (* never unfold wp_def just rules *)

definition Sum :: com where
"Sum \<equiv> 
 ''x'' ::= N 0;;
 WHILE Less (N 0) (V ''n'') DO (
  ''x'' ::= Plus (V ''x'') (V ''n'') ;;
  ''n'' ::= Plus (V ''n'') (N (-1))
 )"

fun sum :: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1 ) + i)"

lemma sum_simps[simp]:
"0 < i \<Longrightarrow> sum i = sum (i - 1) + i"
"i \<le> 0 \<Longrightarrow> sum i = 0"
  by simp+

lemmas [simp del] = sum.simps

lemma "wlp Sum (\<lambda>s'. s' ''x'' = sum (s ''n'')) s"
  unfolding Sum_def
  unfolding wlp_eq
  (*here we annotate the invariant*)
  apply(subst wlp_annotate_while[
   where I = "\<lambda>s'. sum (s' ''n'') = sum (s ''n'') - (s' ''x'')  "  ])
  apply smartvcg
done

lemma
fwd_Assign: "P s \<Longrightarrow> wp (x ::= a) (\<lambda>s'. \<exists> s. P s \<and> s' = s(x := aval a s)) s"
  unfolding wp_assign_eq
  apply auto
  done

lemmas fwd_Assign' = wp_conseq[OF fwd_Assign]

lemma  "a = s ''a'' \<Longrightarrow> b = s ''b'' \<Longrightarrow>
        wp Max (\<lambda>s'. s' ''c'' = max a b \<and> s ''a'' = a \<and> s ''b'' = b) s"
  unfolding Max_def
  apply(rule wp_ifI)
  apply(rule fwd_Assign', simp)+
   apply auto
  done
  
 

end