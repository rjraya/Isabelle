theory Defs
  imports "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP2/vcg/VCG"
begin

fun factorial :: "int \<Rightarrow> int" where
  "factorial i = (if i \<le> 0 then 1 else i * factorial (i - 1))"

fun fib :: "int \<Rightarrow> int" where
  "fib i = (if i \<le> 0 then 0 else if i = 1 then 1 else fib (i - 2) + fib (i - 1))"

lemma fib_simps[simp]:
  "i \<le> 0 \<Longrightarrow> fib i = 0"
  "i = 1 \<Longrightarrow> fib i = 1"
  "i > 1 \<Longrightarrow> fib i = fib (i - 2) + fib (i - 1)"
  by simp+

lemmas [simp del] = fib.simps

end