theory MiniHales
  imports  "HOL-Algebra.Group"  "HOL-Library.Bit" "HOL-Library.Rewrite"
begin

class ell_field = field + 
  assumes two_not_zero: "2 \<noteq> 0"

locale curve_addition =  
  fixes c d :: "'a::ell_field"
  fixes t' :: "'a::ell_field"
  assumes c_eq_1: "c = 1"
  assumes t_intro: "d = t'^2"
  assumes t_ineq: "t'^2 \<noteq> 1" "t' \<noteq> 0"
begin   

definition t where "t = t'" 

fun add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
 "add (x1,y1) (x2,y2) =
    ((x1*x2 - c*y1*y2) div (1-d*x1*y1*x2*y2), 
     (x1*y2+y1*x2) div (1+d*x1*y1*x2*y2))"

fun ext_add :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
 "ext_add (x1,y1) (x2,y2) =
    ((x1*y1-x2*y2) div (x2*y1-x1*y2),
     (x1*y1+x2*y2) div (x1*x2+y1*y2))"

definition delta_x :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_x x1 y1 x2 y2 = x2*y1 - x1*y2"
definition delta_y :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_y x1 y1 x2 y2 = x1*x2 + y1*y2"
definition delta' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta' x1 y1 x2 y2 = delta_x x1 y1 x2 y2 * delta_y x1 y1 x2 y2"

definition delta_plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_plus x1 y1 x2 y2 = 1 + d * x1 * y1 * x2 * y2"

definition delta_minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta_minus x1 y1 x2 y2 = 1 - d * x1 * y1 * x2 * y2"

definition delta :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "delta x1 y1 x2 y2 = (delta_plus x1 y1 x2 y2) * 
                      (delta_minus x1 y1 x2 y2)"

definition e' where "e' x y = x^2 + y^2 - 1 - t^2 * x^2 * y^2"

lemma t_expr: "t^2 = d" "t^4 = d^2" using t_intro t_def by auto


ML \<open>
fun basic_equalities assms ctxt z1' z3' =
let 
  (* Basic equalities *)

  val th1 = @{thm fstI}  OF  [(nth assms 0)]
  val th2 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "fst::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 2)])
  val x1'_expr = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop 
                             (HOLogic.mk_eq (@{term "x1'::'a"},HOLogic.mk_fst z1')))
                            (fn _ =>
                                    EqSubst.eqsubst_tac ctxt [1] [th1] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th2] 1
                                    THEN simp_tac ctxt 1)
  val th3 = @{thm sndI}  OF  [(nth assms 0)]
  val th4 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "snd::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 2)])
  val y1'_expr = Goal.prove ctxt [] []
                                 (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "y1'::'a"},HOLogic.mk_snd z1')))
                            (fn _ => EqSubst.eqsubst_tac ctxt [1] [th3] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th4] 1
                                    THEN simp_tac ctxt 1)
  val th5 = @{thm fstI}  OF  [(nth assms 1)]
  val th6 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "fst::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 3)])
  val x3'_expr = Goal.prove ctxt [] []
                                 (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "x3'::'a"},HOLogic.mk_fst z3')))
                            (fn _ => EqSubst.eqsubst_tac ctxt [1] [th5] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th6] 1
                                    THEN simp_tac ctxt 1)
  
  val th7 = @{thm sndI}  OF  [(nth assms 1)]
  val th8 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "snd::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 3)])
  val y3'_expr = Goal.prove ctxt [] []
                                 (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "y3'::'a"},HOLogic.mk_snd z3')))
                            (fn _ => EqSubst.eqsubst_tac ctxt [1] [th7] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th8] 1
                                    THEN simp_tac ctxt 1)
in 
  (x1'_expr,y1'_expr,x3'_expr,y3'_expr)
end

fun rewrite_procedures ctxt =
let
  val rewrite1 =
    let 
      val pat = [Rewrite.In,Rewrite.Term 
                  (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),
                Rewrite.At]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric]}) 1 
     end
  
  val rewrite2 =
    let 
      val pat = [Rewrite.In,Rewrite.Term 
                  (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),
                 Rewrite.In]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric] 
                               }) 1 
     end;

  val rewrite3 =
     let 
      val pat = [Rewrite.In,Rewrite.Term (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ 
                                          Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),Rewrite.At]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric]}) 1 
     end
  
  val rewrite4 =
    let 
      val pat = [Rewrite.In,Rewrite.Term (@{const divide('a)} $ Var (("c", 0), \<^typ>\<open>'a\<close>) $ 
                                         Rewrite.mk_hole 1 (\<^typ>\<open>'a\<close>), []),Rewrite.In]
      val to = NONE
     in
      CCONVERSION (Rewrite.rewrite_conv ctxt (pat, to) @{thms delta_x_def[symmetric] delta_y_def[symmetric] 
                                                              delta_minus_def[symmetric] delta_plus_def[symmetric]}) 1 
     end 
in 
  (rewrite1,rewrite2,rewrite3,rewrite4)
end


fun concrete_assoc first second third fourth =
let
 
  val ctxt0 = @{context};
  val ctxt = ctxt0;
  val (_,ctxt) = Variable.add_fixes ["z1'","x1'","y1'",
                                     "z3'","x3'", "y3'", 
                                     "x1", "y1", "x2", "y2", "x3", "y3"] ctxt

  val z1' = if first = "ext" then @{term "ext_add (x1,y1) (x2,y2)"} else @{term "add (x1,y1) (x2,y2)"}
  val z3' = if fourth = "ext" then @{term "ext_add (x2,y2) (x3,y3)"} else @{term "add (x2,y2) (x3,y3)"}
  val lhs = if second = "ext" then (fn z1' => @{term "ext_add"} $ z1' $ @{term "(x3::'a,y3::'a)"}) 
                              else (fn z1' => @{term "add"} $ z1' $ @{term "(x3::'a,y3::'a)"})
  val rhs = if third = "ext" then (fn z3' => @{term "ext_add (x1,y1)"} $ z3')
                             else (fn z3' => @{term "add (x1,y1)"} $ z3') 

  val delta1 = case z1' of @{term "ext_add"} $ _ $ _ => [@{term "delta' x1 y1 x2 y2"},@{term "delta_x x1 y1 x2 y2"},@{term "delta_y x1 y1 x2 y2"}]
                         | @{term "add"} $ _ $ _     => [@{term "delta x1 y1 x2 y2"},@{term "delta_minus x1 y1 x2 y2"},@{term "delta_plus x1 y1 x2 y2"}]
                         | _ => [] (* fix, raise some appropriate exception *)
  val delta2 = case (lhs @{term "z1'::'a \<times> 'a"}) of 
                           @{term "ext_add"} $ _ $ _ => [@{term "delta_x x1' y1' x3 y3"},@{term "delta_y x1' y1' x3 y3"}]
                         | @{term "add"} $ _ $ _     => [@{term "delta_minus x1' y1' x3 y3"},@{term "delta_plus x1' y1' x3 y3"}]
                         | _ => [] (* fix, raise some appropriate exception *)
  val delta3 = if third = "ext" then [@{term "delta_x x1 y1 x3' y3'"},@{term "delta_y x1 y1 x3' y3'"}]
                                else [@{term "delta_minus x1 y1 x3' y3'"},@{term "delta_plus x1 y1 x3' y3'"}]

  val delta4 = if fourth = "ext" then [@{term "delta' x2 y2 x3 y3"},@{term "delta_x x2 y2 x3 y3"},@{term "delta_y x2 y2 x3 y3"}]
                                 else [@{term "delta x2 y2 x3 y3"},@{term "delta_minus x2 y2 x3 y3"},@{term "delta_plus x2 y2 x3 y3"}]
 (*TODO: simple combinator for this*)
  val assms3 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_eq(@{term "z1'::'a \<times> 'a"},z1')))
  val assms4 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_eq(@{term "z3'::'a \<times> 'a"},z3')))
  val assms5 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta1 1,@{term "0::'a"}))))
  val assms6 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta1 2,@{term "0::'a"}))))
  val assms7 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta4 1,@{term "0::'a"}))))
  val assms8 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta4 2,@{term "0::'a"}))))
  val assms9 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta2 0,@{term "0::'a"}))))
  val assms10 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta2 1,@{term "0::'a"}))))
  val assms11 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta3 0,@{term "0::'a"}))))
  val assms12 = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (nth delta3 1,@{term "0::'a"}))))

  val (assms,ctxt) = Assumption.add_assumes 
                         [@{cprop "z1' = (x1'::'a,y1'::'a)"}, @{cprop "z3' = (x3'::'a,y3'::'a)"},
                          assms3,assms4,assms5,assms6,assms7, assms8,assms9, assms10,assms11, assms12,
                          @{cprop "e' x1 y1 = 0"}, @{cprop "e' x2 y2 = 0"}, @{cprop "e' x3 y3 = 0"} 
                         ] ctxt;

  val th1 = @{thm fstI}  OF  [(nth assms 0)]
  val th2 = Thm.instantiate' [SOME @{ctyp "'a"}] 
                             [SOME @{cterm "fst::'a\<times>'a \<Rightarrow> 'a"}]  
                             (@{thm arg_cong} OF [(nth assms 2)])
  val _ = @{print} th1
  val _ = @{print} th2
in
 (* (singleton (Proof_Context.export ctxt ctxt0) goal,x1'_expr)*)
  Goal.prove ctxt [] [] (HOLogic.mk_Trueprop 
                             (HOLogic.mk_eq (@{term "x1'::'a"},HOLogic.mk_fst z1')))
                            (fn _ =>
                                    EqSubst.eqsubst_tac ctxt [1] [th1] 1
                                    THEN EqSubst.eqsubst_tac ctxt [1] [th2] 1
                                    THEN simp_tac ctxt 1)
end

\<close>


ML \<open>
concrete_assoc "ext" "ext" "add" "add"
\<close>


end

end