theory Seminar3
  imports Complex_Main
begin
 
section\<open>ISAR\<close>

subsection\<open>Running example\<close>
text\<open>
 ISAR stands for Intelligible semi-automated language.

 It makes proofs look like normal mathematical proofs.

 Here is a proof of Cantor's theorem:

 There cannot be a surjective mapping between a set and its power set
\<close>
lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

subsection\<open>Abbreviations\<close>

text\<open>this\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text\<open>then = from this\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then show "False" by blast
qed

text\<open>hence = then have, thus = then show\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed

subsection\<open>Proof patterns\<close>

text\<open>
 How would proof:

 1. P \<longleftrightarrow> Q
 2. A = B (as sets)
 3. P (contradiction, case distinction,...)
\<close>

lemma "P \<longleftrightarrow> Q"
proof
  assume "P" 
  show "Q" sorry
next
  assume "Q"
  show "P" sorry
qed

lemma "A = (B::'a set)"
proof
  show "A \<subseteq> B" sorry
next
  show "B \<subseteq> A" sorry
qed

lemma "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
  show "a \<in> B" sorry
qed

text\<open>Contradiction\<close>

lemma P
proof (rule ccontr)
  assume "\<not>P"
  show "False" sorry
qed

text\<open>Case distinction\<close>

lemma "R"
proof cases
  assume "P"
  show "R" sorry
next
  assume "\<not> P"
  show "R" sorry
qed

lemma "R"
proof -
  have "P \<or> Q" sorry
  then show "R"
  proof
    assume "P"
    show "R" sorry
  next
    assume "Q"
    show "R" sorry
  qed
qed

text\<open>
 obtain example
 obtain is used to eliminate the existential quantifier
\<close>

lemma "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed


text\<open>Interactive exercise:\<close>

lemma 
  assumes "\<exists>x. \<forall>y. P x y" 
  shows "\<forall>y. \<exists>x. P x y"
sorry


subsection \<open>(In)Equation Chains\<close>

lemma "(0::real) \<le> x^2 + y^2 - 2*x*y"
proof -
  have "0 \<le> (x - y)^2" by simp
  also have "\<dots> = x^2 + y^2 - 2*x*y"
    by(simp add: numeral_eq_Suc algebra_simps)
  finally show "0 \<le> x^2 + y^2 - 2*x*y" .
qed

text\<open>Interactive exercise:\<close>

lemma
  fixes x y :: real
  assumes "x \<ge> y" "y > 0"
  shows "(x - y) ^ 2 \<le> x^2 - y^2"
proof -
  have "(x - y) ^ 2 = x^2 + y^2 - 2*x*y"
    by(simp add: numeral_eq_Suc algebra_simps)
  show "(x - y) ^ 2 \<le> x^2 - y^2"
    sorry
qed

subsection\<open>Pattern matching and ?-variables\<close>

lemma "\<exists> x y :: int. x < z \<and> z < y" (is "\<exists> x y. ?P x y")
proof -
  have "?P (z - 1) (z + 1)" by arith
  thus ?thesis by blast
qed

subsection\<open>Example: Top Down Proof Development\<close>

lemma "\<exists>ys zs. xs = ys @ zs \<and>
          (length ys = length zs \<or> length ys = length zs + 1)"
sorry

section\<open>What to do next?\<close>

text\<open>
 1. Learn Isabelle and Semantics together!
 http://concrete-semantics.org/
 https://github.com/rjraya/Isabelle
 
 2. Participate in monthly challenges.
 http://competition.isabelle.systems/competitions/

 3. Contribute to the Archive of Formal Proofs.
 https://www.isa-afp.org/index.html

 4. If you really can't live with two arrows for implication:
  \<Longrightarrow> \<longrightarrow>
 watch this video:
 https://www.youtube.com/watch?v=GNfwde3lYyg
 
 5. If you are really stuck in structuring your formalization, 
 watch the above video or do the tutorial on locales of this page:
 
 http://isabelle.in.tum.de/documentation.html

 6. If you have questions regarding Isabelle:

 6.1 Ask on StackOverflow:
  https://stackoverflow.com/questions/tagged/isabelle
 6.2 Ask on the Isabelle's mailing list:
  https://lists.cam.ac.uk/mailman/listinfo/cl-isabelle-users

 6. If you need to talk to someone about your addiction to theorem
 proving, talk to me at:

 rjraya@correo.ugr.es
 raya@in.tum.de
\<close>

end