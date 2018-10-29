theory Overview_Demo
imports Main
begin

(* A simple comment *)

text {* This is also a comment but it generates nice \LaTeX-text! *}

text {* Note that variables and constants (eg True, &) are displayed differently.  *}

term "True"
term "False"
term "true"
term "True & False"
term "True & false"

value "True & False"
value "True & P"

(* To display types in jedit: press ctrl (Mac: cmd) and hover over text.
   To view the definition of a constant: press ctrl (Mac: cmd) and click on the text.
*)

text {* Warning: "+" and numbers are overloaded: *}

term "n + n = 0"
term "(n::nat) + n = 0"

(*Try this:

term "True + False"

Terms must be type correct!*)

text{* Type inference: *}

term "f (g x) y"
term "h (%x. f(g x))"
term "%x. x + x"

end
