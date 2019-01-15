

(* NOTE - this file linked multiple places, careful when editing *)

structure OldGoals = Goals ;

val () = ThyLoad.add_path "$ISABELLE_HOME_USER/2005/gen" ;
val () = ThyLoad.add_path "$ISABELLE_HOME_USER/2005/monad" ;
val () = ThyLoad.add_path "$ISABELLE_HOME/src/HOL/Lattice" ;
val () = ThyLoad.add_path "$ISABELLE_HOME/src/HOL/Library" ;
ThyLoad.show_path();

val () = ThyInfo.use_thy "HOL_Gen" ;
(*
val () = ThyInfo.use_thy "all" ;
*)

