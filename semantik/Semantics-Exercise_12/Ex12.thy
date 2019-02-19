theory Ex12
  imports "/cygdrive/c/Users/rraya/Isabelle/semantics1819_public/IMP/Types"
begin

fun atype :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty option" where
"atype \<Gamma> (Ic i) = Some Ity" 
|"atype \<Gamma> (Rc r) = Some Rty" 
|"atype \<Gamma> (V x) = Some (\<Gamma> x)"
|"atype \<Gamma> (Plus a1 a2) = (
  case (atype \<Gamma> a1,atype \<Gamma> a2) of 
   (Some \<tau>1, Some \<tau>2) \<Rightarrow> (if \<tau>1 = \<tau>2 then Some \<tau>1 else None)
  | _ \<Rightarrow> None
 )"

lemma atyping_atype: "(\<Gamma> \<turnstile> a : \<tau>) = (atype \<Gamma> a = Some \<tau>)"
  apply(induction a)
  apply(auto split: option.splits)
  done

fun bok :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" where
"bok \<Gamma> (Bc v) = True"
| "bok \<Gamma> (Not b) = bok \<Gamma> b"
| "bok \<Gamma> (And b1 b2) \<longleftrightarrow> (bok \<Gamma> b1) \<and> (bok \<Gamma> b2)"
| "bok \<Gamma> (Less a1 a2) = ( 
    case (atype \<Gamma> a1,atype \<Gamma> a2) of 
     (Some \<tau>1, Some \<tau>2) \<Rightarrow> \<tau>1 = \<tau>2 
  | _ \<Rightarrow> False
)"

lemma btyping_bok: "(\<Gamma> \<turnstile> b) = bok \<Gamma> b"
  apply(induction b)
  apply(auto split: option.splits simp: atyping_atype)
done

fun cok :: "tyenv \<Rightarrow> com \<Rightarrow> bool" where
"cok \<Gamma> SKIP = True" 
| "cok \<Gamma> (x::=a) = (atype \<Gamma> a = Some (\<Gamma> x))"
| "cok \<Gamma> (c1;;c2) = (cok \<Gamma> c1 \<and> cok \<Gamma> c2)"
| "cok \<Gamma> (IF b THEN c1 ELSE c2) = (bok \<Gamma> b \<and> cok \<Gamma> c1 \<and> cok \<Gamma> c2)"
| "cok \<Gamma> (WHILE b DO c) = (bok \<Gamma> b \<and> cok \<Gamma> c)"

lemma ctyping_cok: "(\<Gamma> \<turnstile> c) = cok \<Gamma> c"
  apply(induction c)
  apply(auto simp: atyping_atype btyping_bok)
done


end