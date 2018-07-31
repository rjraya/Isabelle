theory Exercises2
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: 'a tree \<Rightarrow> 'a list where 
"contents Tip = []"
"contents (Node l a r) = contents l ++ a ++ contents r"


end

