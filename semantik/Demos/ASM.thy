section "Stack Machine and Compilation"

theory ASM
imports AExp
begin

subsection "Stack Machine"

datatype instr = LOADI val | LOAD vname | ADD

(* the start of the list is the top of the stack *)
type_synonym stack = "val list"

(*
we can leave the underflow unresolved or
give some arbitrary value for this value

by default the system will assigned undefined

stk # undefined = undefined
undefined = undefined

undefined is just a constant of this type, in this
case stack

also we could model it by returning stack option
and returning none in these cases
*)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk  = n # stk " |
"exec1 (LOAD x) s stk  = s x # stk " |
"exec1  ADD _ (i # j # stk)  = (i + j) # stk "

(*
 exec1 i s (exec is s stk) is a foldleft operation
*)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

lemma "exec is s stk = fold (\<lambda>i stk. exec1 i s stk) is stk" 
apply(induction "is" arbitrary: stk)
apply(auto)
done

value "exec [LOADI 5, LOAD ''y'', ADD] <''x'' := 42, ''y'' := 43> [50]"


subsection "Compilation"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

value "comp (Plus (Plus (V ''x'') (N 1)) (V ''z''))"


(*
we are missing lemmas about append which could have
been avoided if one provided the definition with fold

lemma "exec (is1@is2) s stk = exec is2 s (exec is1 s stk)"
lemma "exec (is1@is2) s stk = (let stk = exec is1 s stk;stk = exec is2 s stk in stk)"

this could be model by a state monad in Haskell
*)
lemma exec_lem[simp]:"exec (is1@is2) s stk = (let stk = exec is1 s stk;stk = exec is2 s stk in stk)"
(*
induction has to be done on left because this is the
order followed by pattern match
*)
apply(induction is1 arbitrary: stk)
apply(auto)
done

theorem exec_append[simp]: "exec (comp a) s stk = aval a s # stk"
apply(induction a arbitrary: stk)
apply(auto)
done

theorem exec_comp: "exec (comp a) s [] =[aval a s]" by auto


end
