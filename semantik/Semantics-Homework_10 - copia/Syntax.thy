theory Syntax
  imports "Main"
begin

text \<open>
 We formalize the syntax of GCL following the one of IMP introducing the new constructs.
\<close>

section \<open>Syntactic definition of GCL\<close>

type_synonym vname = string
type_synonym val = int

text \<open>
 There is no need to introduce a new configuration fail (as in Winskel, chapter 14).
 This is because guarded commands always act in communication with if and do.
 These constructs handle the behaviour of the command.
\<close>

type_synonym state = "vname \<Rightarrow> val"

datatype aexp = 
      N int 
    | V vname
    | Unop "int \<Rightarrow> int" aexp 
    | Binop "int \<Rightarrow> int \<Rightarrow> int" aexp aexp
    
datatype bexp = 
      Bc bool 
    | Not bexp 
    | BBinop "bool \<Rightarrow> bool \<Rightarrow> bool" bexp bexp 
    | Cmpop "int \<Rightarrow> int \<Rightarrow> bool" aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" 
| "aval (V x) s = s x" 
| "aval (Unop f a\<^sub>1) s = f (aval a\<^sub>1 s)"
| "aval (Binop f a\<^sub>1 a\<^sub>2) s = f (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v" 
| "bval (Not b) s = (\<not> bval b s)" 
| "bval (BBinop f b\<^sub>1 b\<^sub>2) s = f (bval b\<^sub>1 s) (bval b\<^sub>2 s)" 
| "bval (Cmpop f a\<^sub>1 a\<^sub>2) s = f (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

text \<open>
A guarded command gc is a list of the form: \<open>(b\<^sub>1 \<rightarrow> c\<^sub>1) | \<dots> | (b\<^sub>n \<rightarrow> c\<^sub>n)\<close>

To execute it, one evaluates which boolean conditions \<open>b\<^sub>i\<close> are true. 
If this set is empty then the execution fails (this is handled by outer constructs).
Otherwise, one of the associated commands is executed non-deterministically.

Abort does not yield a final state from any initial state. There is no need to represent
this explicitely as a command since there will be no rules associated with it. 

IfBlock gc executes as gc if execution of gc does not fail. Otherwise, it acts like abort. 

DoWhile gc executes repeatedly gc while gc continues not to fail. It terminates when gc fails. 
It acts like skip if the guarded command fails initially.
\<close>

datatype com = 
      SKIP
    | Assign vname aexp              ("_ ::= _" [1000, 61] 61)      
    | Seq com com                    ("_;;/ _"  [61, 60] 60)
    | IfBlock "(bexp \<times> com) list"    ("IF _ FI" [61] 61)        
    | DoWhile "(bexp \<times> com) list"    ("DO _ OD" [61] 61)

end