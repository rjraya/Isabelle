theory Submission
  imports Defs
begin

text \<open>Delta Encoding\<close>
text \<open>
  We want to encode a list of integers as follows: 
    The first element is unchanged, and every next element 
    only indicates the difference to its predecessor.

    For example: (Hint: Use this as test cases for your spec!)
      \<^item> \<open>enc [1,2,4,8] = [1,1,2,4]\<close>
      \<^item> \<open>enc [3,4,5] = [3,1,1]\<close>
      \<^item> \<open>enc [5] = [5]\<close>
      \<^item> \<open>enc [] = []\<close>
    

    Background: This algorithm may be used in lossless data compression, 
      when the difference between two adjacent values is expected to be 
      small, as e.g. in audio data, image data, or sensor data.

      It typically requires much less space to store the small deltas than  the absolute values. 

      Disadvantage: If the stream gets corrupted, recovery is only
possible  when the next absolute value is transmitted. For this reason,
in practice, one will submit the current absolute value from
time to time. (This is not modeled in this exercise!)
\<close>
text \<open>
Specify a function to encode a list with delta-encoding.   
  The first argument is used to represent the previous value, and can
be initialized to 0.\<close>

fun denc :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "denc prv (x#xs) = (x-prv)#(denc x xs)" |
  "denc prv Nil    = Nil"

value "denc 0 [1,2,4,8] = [1,1,2,4]"
value "denc 0 [3,4,5]   = [3,1,1]"
value "denc 0 [5]       = [5]"
value "denc 0 []        = []"

text \<open>
Specify the decoder. Again, the first argument represents the
previous decoded value, and can be initialized to 0.\<close>

fun ddec :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "ddec prv (x#xs) = (x+prv)#(ddec (x+prv) xs)" |
  "ddec prv Nil    = Nil"

value "ddec 0 [1,1,2,4] = [1,2,4,8]"
value "ddec 0 [3,1,1]   = [3,4,5]"
value "ddec 0 [5]       = [5]"
value "ddec 0 []        = []"

text \<open>
Show that encoding and then decoding yields the same list. \<^emph>\<open>Hint:\<close>
The lemma will need generalization.\<close>

lemma decode_code_general: "ddec a (denc a l) = l"
apply(induction l arbitrary: a)
apply(auto)
done

lemma decode_code: "ddec 0 (denc 0 l) = l" 
apply(simp add: decode_code_general)
done

text \<open>Boolean Expressions With Equality\<close>
text \<open>
  Our current version of Boolean expressions is missing an equality operator on arithmetic expressions.
  In this exercise your task is to define a function \<open>beq\<close> that, given two arithmetic expressions
  \<open>a\<^sub>1\<close> and \<open>a\<^sub>2\<close>, constructs a Boolean expression \<open>beq a\<^sub>1 a\<^sub>2\<close> such that:
\<close>

definition beq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "beq a1 a2 = (And (Not (Less a1 a2)) (Not (Less a2 a1)))"

lemma bval_beq:
  "bval (beq a1 a2) s \<longleftrightarrow> aval a1 s = aval a2 s"  
  apply(auto simp: beq_def)
done


text \<open>Models for Boolean Formulas\<close>
text \<open>
  Consider the following datatype modeling Boolean formulas:
\<close>

datatype 'a bexp' = V 'a | And "'a bexp'" "'a bexp'" | Not "'a bexp'" | TT | FF

text \<open>Define a function \<open>sat\<close> that decides whether a given assignment satisfies a formula:\<close>
fun sat :: "'a bexp' \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "sat (V x) i       \<longleftrightarrow> i x = True" |
  "sat TT _          \<longleftrightarrow> True" |
  "sat FF _          \<longleftrightarrow> False" |
  "sat (Not f) i     \<longleftrightarrow> \<not>(sat f i)" |
  "sat (And f1 f2) i \<longleftrightarrow> (sat f1 i) \<and> (sat f2 i)"

text \<open>Define a function \<open>models\<close> that computes the set of satisfying assignments for a given
Boolean formula:\<close>

fun models :: "'a bexp' \<Rightarrow> ('a \<Rightarrow> bool) set"
where
  "models (V x)       = {\<sigma>. \<sigma> x}"                  |
  "models TT          = UNIV"                 |
  "models FF          = {}"                        |
  "models (Not f)     = UNIV - (models f)"    |
  "models (And f1 f2) = (models f1) \<inter> (models f2)"

text \<open>Here @{thm UNIV_def}. Fill in the remaining cases!
\<^emph>\<open>Hint:\<close> You can use the set operators \<open>-\<close>, \<open>\<inter>\<close>, \<open>\<union>\<close> for complement/difference, intersection,
and union of sets.\<close>

text \<open>Finally prove that a formula is a satisfying assignment for a formula \<open>\<phi>\<close> iff it is contained
in \<open>models \<phi>\<close>:\<close>

lemma models_correct:
  "sat \<phi> \<sigma> \<longleftrightarrow> \<sigma> \<in> models \<phi>"
apply(induction \<phi>)
apply(auto)
done

text \<open>Simplifying Boolean Formulas (Bonus)\<close>
text \<open>\<^emph>\<open>Note:\<close> This is a bonus exercise worth three additional points.
  In the end, the total number of achievable points will be the sum of all the points you can
  get for all regular exercises. When we calculate the percentage of the total points you reached,
  we will just add the bonus points on top of the points you got in the regular exercises.
\<close>

text \<open>In this exercise, we want to simplify the Boolean formulas defined in the previous exercise
by removing the constants @{term FF} and @{term TT} from them where possible.
We will say that a formula is \<^emph>\<open>simplified\<close> if does not contain a constant or if it is
@{term FF} or @{term TT} itself.
\<close>
fun has_const where
  "has_const TT = True"
| "has_const FF = True"  
| "has_const (Not a) = has_const a"  
| "has_const (And a b) \<longleftrightarrow> has_const a \<or> has_const b"  
| "has_const _ = False"  

definition "simplified \<phi> \<longleftrightarrow> \<phi> = TT \<or> \<phi> = FF \<or> \<not> has_const \<phi>"

fun simplify :: "'a bexp' \<Rightarrow> 'a bexp'" where
  "simplify (V x) = (V x)" |
  "simplify TT = TT" |
  "simplify FF = FF" |
  "simplify (Not f)  = 
    (let fsimp = simplify(f) in 
     (case fsimp of 
      TT \<Rightarrow> FF |
      FF \<Rightarrow> TT |
      _  \<Rightarrow> (Not fsimp)
     )
    )" |
  "simplify (And f1 f2) = 
    (let (fsimp1, fsimp2) = (simplify(f1),simplify(f2)) in
     (case (fsimp1,fsimp2) of
      (TT,f) \<Rightarrow> f  | 
      (f,TT) \<Rightarrow> f  |
      (FF,f) \<Rightarrow> FF |
      (f,FF) \<Rightarrow> FF |
      _      \<Rightarrow> (And fsimp1 fsimp2)
     )
    )"
      

text \<open>Define a function @{term [show_types] simplify} that simplifies Boolean formulas and
prove that it produces only simplified formulas:\<close>

lemma simplify_simplifies: "simplified (simplify \<phi>)"
  apply(induction \<phi> rule: simplify.induct)
  apply(simp add: simplified_def)
  apply(simp add: simplified_def)
  apply(simp add: simplified_def)
  (* Now we have to solve And and Not 
     We leave the process indicated:
     the key is to first expand the lets*)
  apply(auto simp add: Let_def)
  apply(simp split: bexp'.split)
  apply(auto split: bexp'.split)
  apply(auto simp add: simplified_def) 
done  


text \<open>Even more importantly, you need to prove that \<open>simplify\<close> does not alter the semantics of
the formula:\<close>

lemma notsimp: "models (simplify \<phi>) = models \<phi> \<Longrightarrow> models (simplify (Not \<phi>)) = models (Not \<phi>)"
  apply(simp)
  apply(simp add: Let_def)
  apply(simp split: bexp'.split)
  apply(intro conjI)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
done
  

lemma andlemma: 
      "models (simplify f1) = models f1 \<Longrightarrow>
       models (simplify f2) = models f2 \<Longrightarrow> 
       models (simplify (And f1 f2)) = models (And f1 f2)"
  apply(simp)
  apply(simp split: bexp'.split)
  apply(intro conjI)
  apply(cases "simplify f1")
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
  apply(force)
done
 
lemma simplify_correct: "models (simplify \<phi>) = models \<phi>"
  apply(induction \<phi> rule: models.induct)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(rule notsimp)
  apply(simp)
  apply(rule andlemma)
  apply(auto)
done
  

end