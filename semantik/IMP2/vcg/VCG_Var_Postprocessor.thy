section \<open>Program Variables to Isabelle Variables\<close>
theory VCG_Var_Postprocessor
imports "../Semantics" "../lib/Subgoal_Focus_Some"
begin
  definition VBIND :: "state \<Rightarrow> vname \<Rightarrow> val \<Rightarrow> bool"
    where "VBIND s x v \<equiv> s x = v"
    
  lemma VBINDD: "VBIND s x v \<Longrightarrow> s x = v" unfolding VBIND_def ASSUMPTION_def by auto
  lemma VBINDI:
    assumes "\<And>v. VBIND s x v \<Longrightarrow> P"
    shows "P" using assms
    unfolding VBIND_def by simp
  
  
  ML \<open>
    (*
      Postprocess VCs to convert states applied to variable names to actual logical variables.
    *)
    structure VC_Postprocessor = struct
    
      (* Create rule to introduce VBIND, with specified instantiation *)
      fun VBINDI_rl ctxt s x n = let    
      
        (* Rough approximation to hit \<And>v. \<dots> *)
        fun rn (Abs ("v",T,t)) = Abs (n,T,t)
          | rn (a$b) = rn a $ rn b
          | rn t = t
    
        val (s,x) = apply2 (Thm.cterm_of ctxt) (s,x)
          
        val thm = @{thm VBINDI}
          |> Drule.infer_instantiate' ctxt [SOME s,SOME x]
        
        val t = thm  |> Thm.prop_of |> rn
        val thm' = Thm.renamed_prop t thm
      in thm' end
    
      (* Guess suffix from name, e.g. "a\<^sub>3" \<mapsto> "\<^sub>3" *)  
      val guess_suffix = let
        val sfxs = ["'","\<^sub>","\<^sup>","\<^bsub>","\<^bsup>"]
      in  
        Symbol.explode #> chop_prefix (not o member op = sfxs) #> snd #> implode
      end
  
      (* Introduce VBIND. Try to guess appropriate name for introduced Isabelle variable *)
      fun VBINDI_rl_heur ctxt (sname,s,x) = let
      
        fun name_of (Free (n,_)) = n
          | name_of _ = "v"
    
        val n = the_default (name_of x) (try HOLogic.dest_string x)
        
        val n = n ^ guess_suffix sname
      in
        VBINDI_rl ctxt s x n
      end
    
      fun add_state_candidates ((s as Free (n,@{typ state})) $ x) =
        if can HOLogic.dest_string x then apfst (insert op= (n,s,x))
        else apsnd (insert op= s) #> add_state_candidates x
      | add_state_candidates (s as Free (_,@{typ state})) = apsnd (insert op= s)
      | add_state_candidates (a$b) = add_state_candidates a #> add_state_candidates b
      | add_state_candidates (Abs (_,_,t)) = add_state_candidates t
      | add_state_candidates _ = I
      
      fun compute_state_candidates (good,bad) = subtract (fn (b,(_,n,_)) => b=n) bad good
      
      val insert_vbind_tac = Subgoal.FOCUS_PARAMS (fn {context=ctxt, concl, params, ...} => let
          val conclt = Thm.term_of concl
          val svars = add_state_candidates conclt ([],[]) 
            |> compute_state_candidates
            
          val rename_tab = params |> map (apsnd (Thm.term_of) #> swap) |> Termtab.make 
    
          val pairs = map (fn (ns,s,x) => (the_default ns (Termtab.lookup rename_tab s), s, x)) svars
          val tacs = map (resolve_tac ctxt o single o VBINDI_rl_heur ctxt) pairs
                  
        in
          EVERY1 tacs
        end
        )
      
      fun rewr_vbind_tac ctxt = let
        fun is_vbind (Const (@{const_name VBIND},_)$_$_$_) = true | is_vbind _ = false
      in 
        Subgoal_Focus_Some.FOCUS_SOME_PREMS (fn _ => Thm.term_of #> HOLogic.dest_Trueprop #> is_vbind)
          (fn {context=ctxt, prems, ...} => let 
            val thms = map (fn t => @{thm VBINDD} OF [t]) prems
          in 
            Local_Defs.unfold_tac ctxt thms end) ctxt
      
      end
      
      fun remove_vbind_tac ctxt = let 
        (* TODO: Unsafe. Should check that states do not occur elsewhere in goal! *)
        (*val ctxt = put_simpset HOL_basic_ss ctxt addsimps @{thms triv_forall_equality}*)
      in
        SELECT_GOAL (
          REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt @{thms thin_rl[of "VBIND _ _ _"]})
            THEN Local_Defs.unfold_tac ctxt @{thms triv_forall_equality}
          ))
      end
        
      fun postprocess_vc_tac ctxt =
        insert_vbind_tac ctxt
        THEN' rewr_vbind_tac ctxt
        THEN' remove_vbind_tac ctxt
  
    end
  \<close>  
  
  method_setup i_vcg_insert_vbind_tac = \<open>Scan.succeed (SIMPLE_METHOD' o VC_Postprocessor.insert_vbind_tac)\<close>
  method_setup i_vcg_rewr_vbind_tac = \<open>Scan.succeed (SIMPLE_METHOD' o VC_Postprocessor.rewr_vbind_tac)\<close>
  method_setup i_vcg_remove_vbind_tac = \<open>Scan.succeed (SIMPLE_METHOD' o VC_Postprocessor.remove_vbind_tac)\<close>
  method_setup i_vcg_postprocess_vars = \<open>Scan.succeed (SIMPLE_METHOD' o VC_Postprocessor.postprocess_vc_tac)\<close>

end
