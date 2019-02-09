theory Example
  imports Main
begin

lemma aux1: "fold (+) xs (a+b) = a + fold (+) xs (b::nat)"
proof(induction xs arbitrary: b)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have 1: "fold (+) (x # xs) (a + b) = fold (+) xs (x + (a + b))" by simp
  have 2: "... = fold (+) xs (a + (x + b))" using algebra_simps by metis
  from  Cons.IH[of "x + b"]
  have 3: "... = a + fold (+) xs (x + b)" by simp
  from 1 2 3 show ?case by simp
qed

lemma 
 aux2: "(fold (+) (xs@ys) (a+b)) =
  (fold (+) xs a) + (fold (+) (ys::nat list) b)"
proof(induction xs)
  case Nil from aux1 show ?case by simp
next
  case (Cons x xs)
  from this aux1 show ?case by simp  
qed

lemma 
 "(fold (+) (xs@ys) 0) = 
  (fold (+) xs 0) + (fold (+) (ys::nat list) 0)"
  using aux2 by (metis Nat.add_0_right)

end