theory doanddonts
  imports Main
begin
text\<open>
 Advice collection on what to do and not to do with Isabelle
\<close>

section\<open>Syntax\<close>

text\<open>
 1. Do not use \<open>gcd a b = 1\<close> but \<open>coprime a b\<close>

\<close>

section\<open>Debugging\<close>

text\<open>
 Non-matching rules

 If you apply some rule (e.g. with apply (rule \<dots>)) and it fails and 
 you don't understand why, there is a little trick to find out. If you 
 add a using [[unify_trace_failure]] before the apply, you get an error 
 message that indicates where exactly the unification failed. 
\<close>

text\<open>
 Take a look at the GCD theory, keyword consider and atomize
\<close>

section\<open>Searching theorems\<close>

text\<open>We can use ? to refine our queries to find_theorems\<close>

find_theorems "sum _ ?A = sum _ (?f ` ?A)"

section\<open>Modifiers for introduction and elimination rules\<close>

text\<open>http://www21.in.tum.de/~ballarin/fomus/part1/part1.pdf\<close> 

section\<open>The opposite of safe command\<close>

end