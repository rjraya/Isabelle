theory Tree_Demo
imports Main
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

lemma "Leaf \<noteq> Node l x r"
apply auto
done

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Leaf = Leaf" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

value "mirror(Node (Node Leaf a Leaf) b t)"

lemma mirror_mirror[simp]: "mirror(mirror t) = t"
apply(induction t)
apply auto
done

text{* An example of fun: beyond one equation per constructor *}

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a [] = []" |
"sep a [x] = [x]" |
"sep a (x#y#zs) = x # a # sep a (y#zs)"

thm sep.induct
thm sep.simps

function f where "f x = f x + 1" by pat_completeness auto

termination 
  apply(relation R)

value "sep a [x,y,z]"

end
