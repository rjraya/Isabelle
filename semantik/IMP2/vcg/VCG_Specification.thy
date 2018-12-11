section \<open>Specification Commands\<close>
theory VCG_Specification
imports "../Semantics"
keywords "ensures"
     and "program_def" :: thy_decl
     and "program_spec" :: thy_goal
begin

text \<open>Marker that is inserted around all annotations by Specification Parser\<close>
definition "ANNOTATION \<equiv> \<lambda>x. x"

definition VAR :: "('n \<Rightarrow> 'v) \<Rightarrow> 'n \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> 'a" 
  where "VAR s v f \<equiv> f (s v)"


text \<open>Unfold theorems to strip annotations from program, before it is defined as constant\<close>
named_theorems vcg_annotation_defs \<open>Definitions of Annotations\<close>
  
  
  
subsection \<open>Abstraction over Program Variables\<close>
  
    
ML \<open>
  structure Program_Variables = struct

    datatype T = AbsInfo of ((string * string) * term) list * (string * term)
      (* (vname \<times> sfx_name \<times> Free) list \<times> (statename \<times> statev)  *)
  
    val stateN = "\<ss>"           (* Base name for state variable *)
    val nameT = @{typ string}  (* HOL type of variable names *)
    val valueT = @{typ int}    (* HOL type of variable values *)

    val mk_name = HOLogic.mk_string (* Convert from string to HOL varuable name *)
          
    val stateT = nameT --> valueT
      
    fun abstract_var statev ((name, sfx_name), v) t = let
      val T = fastype_of t
      val t = Term.lambda_name (sfx_name,v) t
      val t_name = mk_name name
    in
      Const (@{const_name VAR}, stateT --> nameT --> (valueT --> T) --> T) $ statev $ t_name $ t
    end 
    
    fun get_statev (AbsInfo (_,(_,v))) = v
    
    fun declare_variables names sfx ctxt = let
    
      val sfx_names = map (suffix sfx) names
      val sfx_statename = suffix sfx stateN
      
      val ctxt = ctxt |> Variable.set_body true
      
      val (statev,ctxt) = yield_singleton Variable.add_fixes sfx_statename ctxt
      val statev = Free (statev,stateT)
      val ctxt = Variable.declare_constraints statev ctxt
      
      val (vs,ctxt) = Variable.add_fixes sfx_names ctxt
      val vs = map (fn n => Free (n,valueT)) vs
      val ctxt = fold Variable.declare_constraints vs ctxt
    
    in
      (AbsInfo (names ~~ sfx_names ~~ vs, (sfx_statename, statev)), ctxt)
    end

    fun abstract_vars (AbsInfo (nsvs, (_,statev))) t = let
      val frees = Term.add_frees t [] |> map Free |> Termtab.make_set
      
      fun absv (nss,v) = 
        if Termtab.defined frees v then abstract_var statev (nss,v)
        else I
    
      val t = fold absv nsvs t
    in
      t
    end

    fun abstract_state (AbsInfo (_, (staten,statev))) t = Term.lambda_name (staten, statev) t

    fun abstract vinfo = abstract_vars vinfo #> abstract_state vinfo
      
  end
\<close>
  

subsection \<open>Annotations\<close>
text \<open>The specification parser must interpret the annotations in the program\<close>

definition WHILE_annotI :: "(state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
  ("(WHILE {_} _/ DO _)"  [0, 0, 61] 61) 
  where [vcg_annotation_defs]: "WHILE_annotI (I::state \<Rightarrow> bool) \<equiv> While"
  
lemmas annotate_whileI = WHILE_annotI_def[symmetric]

definition WHILE_annotRVI :: "'a rel \<Rightarrow> (state \<Rightarrow> 'a) \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
    ("(WHILE {_} {_} {_} _/ DO _)"  [0, 0, 0, 0, 61] 61)
  where [vcg_annotation_defs]: "WHILE_annotRVI R V I \<equiv> While" for R V I
  
lemmas annotate_whileRVI = WHILE_annotRVI_def[symmetric]

definition WHILE_annotVI :: "(state \<Rightarrow> nat) \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
  ("(WHILE {_} {_} _/ DO _)"  [0, 0, 0, 61] 61)
where [vcg_annotation_defs]: "WHILE_annotVI V I \<equiv> While" for V I
lemmas annotate_whileVI = WHILE_annotVI_def[symmetric]


subsection \<open>Hoare Triple Syntax\<close>

type_synonym HT'_type = "(state \<Rightarrow> bool) \<Rightarrow> (state \<Rightarrow> com) \<Rightarrow> (state \<Rightarrow> state\<Rightarrow>bool) \<Rightarrow> bool"

definition HT'_partial :: HT'_type
  where "HT'_partial P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wlp (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0)"

definition HT' :: HT'_type
  where "HT' P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wp (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0)"

definition HT 
  where "HT P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wp c (Q s\<^sub>0) s\<^sub>0)"

lemma HT'_eq_HT: "HT' P (\<lambda>_. c) Q = HT P c Q"
  unfolding HT_def HT'_def ..  
  
definition HT_partial
  where "HT_partial P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wlp c (Q s\<^sub>0) s\<^sub>0)"

lemma HT'_partial_eq_HT: "HT'_partial P (\<lambda>_. c) Q = HT_partial P c Q"
  unfolding HT_partial_def HT'_partial_def ..  

lemmas HT'_unfolds = HT'_eq_HT HT'_partial_eq_HT
    
  
(* In-Term notation for Hoare Triples*)   
syntax "_Htriple" :: "cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> logic" ("\<^htriple>_ _ _")
syntax "_Htriple_Partial" :: "cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> cartouche_position \<Rightarrow> logic" ("\<^htriple_partial>_ _ _")


ML \<open>
  structure VCG_Htriple_Syntax = struct
    fun strip_annotations ctxt = 
      Local_Defs.unfold ctxt (Named_Theorems.get ctxt @{named_theorems vcg_annotation_defs})
    
    fun strip_annotations_term ctxt = 
      Thm.cterm_of ctxt #> Drule.mk_term #> 
      strip_annotations ctxt #>
      Drule.dest_term #> Thm.term_of

    fun mk_ANNOTATION t = let val T=fastype_of t in 
      Const (@{const_name ANNOTATION}, T --> T)$t end 
      
    fun dest_ANNOTATION (Const (@{const_name ANNOTATION}, _)$t) = t
      | dest_ANNOTATION t = raise TERM("dest_ANNOTATION", [t]);
      
        
    fun interpret_annotations ctxt0 ctxt v0info vinfo prog_t = let
    
      (* TODO/FIXME: Terms are read independently, which will cause too generic types to be inferred *)
      val plain_term = Term_Annot.read_term ctxt0 
        #> Program_Variables.abstract_vars v0info
        #> mk_ANNOTATION
        
      val with_vars = Term_Annot.read_term ctxt 
        #> Program_Variables.abstract vinfo 
        #> Program_Variables.abstract_vars v0info
        #> mk_ANNOTATION
    
      val mpt = map_types (map_type_tfree (K dummyT))
      
      fun interp_while_annot (t,@{syntax_const "_invariant_annotation"}) (R,V,I) = (R,V,with_vars t :: I)
        | interp_while_annot (t,@{syntax_const "_variant_annotation"})   (R,V,I) = (R,with_vars t :: V,I)
        | interp_while_annot (t,@{syntax_const "_relation_annotation"})  (R,V,I) = (plain_term t :: R,V,I)
        | interp_while_annot (_,ty) _ = error ("Unknown annotation type for while loop: " ^ ty)
      
      fun interp_while_annots annots = let
        val annots = HOLogic.strip_tuple annots
          |> map (apsnd (dest_Const #> fst) o Term_Annot.dest_annotated_term)
          
        val (Rs,Vs,Is) = fold interp_while_annot annots ([],[],[])
         
        val _ = length Rs > 1 andalso error "Multiple relation annotations to loop"
        val _ = length Vs > 1 andalso error "Multiple variant annotations to loop"
        val _ = length Is > 1 andalso error "Multiple invariants not yet supported. Combine them into one"
         
      in 
        case (Rs,Vs,Is) of
          ([],[],[]) => mpt @{const While}
        | ([],[],[I]) => mpt @{const WHILE_annotI} $ I
        | ([],[V],[I]) => mpt @{const WHILE_annotVI} $ V $ I
        | ([R],[V],[I]) => mpt @{const WHILE_annotRVI ('a)} $ R $ V $ I
        | _ => error "Illegal combination of annotations to while loop. The legal ones are: None, I, VI, RVI"
      
      end
      
      fun interp (Const (@{const_abbrev While_Annot},_)$annots) = interp_while_annots annots
        | interp (a$b) = interp a $ interp b
        | interp (Abs (x,T,t)) = Abs (x,T,interp t)
        | interp t = t
    
      val prog_t = interp prog_t

      (* All terms have been abstracted over vinfo, and over the variables of v0info. 
        Now, the whole term is valid wrt vinfo0/ctxt0, which contains declarations 
        of variables0 and state0
        *** TODO: Ideally, one would like to check teh term in a context that does not include 
              variables, but only state decl!
      *)      
      val prog_t = Syntax.check_term ctxt0 prog_t
      
            
      (* We now also abstract over state0, to make the program a function from state0 to an (annotated) command *)
      val res = Program_Variables.abstract_state v0info prog_t

      (* Alternatively, we strip the annotations from the program. This should also remove state0! *)
      val prog_t = strip_annotations_term ctxt prog_t

      val state0v = Program_Variables.get_statev v0info
      
      val _ = exists_subterm (curry op = state0v) prog_t 
        andalso raise TERM("gen_make_htriple: State0 not stripped from program",[prog_t])
            
    in
      (prog_t,res)
    end
    
    (*val HT_constT = @{typ "HT_type"}*)
    val HT_const_total = @{const HT'}
    val HT_const_partial = @{const HT'_partial}
    
    
    fun gen_make_htriple ctxt total mk_pre mk_prog mk_post = let
      val prog_t = mk_prog ctxt
      
      val vnames = IMP_Parser.variables_of prog_t
      
      (* Variable abstractions for postcondition, and program. With intermediate point between v\<^sub>0 \<bullet> v *)
      val (v0info,ctxt_0) = Program_Variables.declare_variables vnames "\<^sub>0" ctxt
      val (vinfo,ctxt_v) = Program_Variables.declare_variables vnames "" ctxt_0

       (* Variable abstractions for precondition *)
      val (vinfo_pre,ctxt_pre) = Program_Variables.declare_variables vnames "" ctxt

      (* Interpret precondition, postcondition, and program annotations, and abstract them over their variables *)
      val pre = mk_pre ctxt_pre 
        |> Program_Variables.abstract vinfo_pre
        
      val post = mk_post ctxt_v 
        |> Program_Variables.abstract vinfo
        |> Program_Variables.abstract v0info
            
      val (stripped_prog_t,prog_t) = interpret_annotations ctxt_0 ctxt_v v0info vinfo prog_t  
      
      (* Assemble Hoare-triple *)
      val HT_const = if total then HT_const_total else HT_const_partial

      val res = HT_const$pre$prog_t$post

    in
      (stripped_prog_t, res)
    end
    

    fun decon_cartouche_ast ((c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p) = (
      case Term_Position.decode_position p of 
        SOME (pos, _) => ((s,pos) (*, fn t => c$t$p*))
      | NONE => raise TERM ("cartouche with invalid pos",[c,p])  
    )
    | decon_cartouche_ast t = raise TERM ("decon_cartouche_ast",[t])  
        
    
    fun htriple_tr total ctxt [tpre, tprog, tpost] = let
    
      (* TODO/FIXME: This can't be the simplest/clean way to parse a term from a cartouche! *)
      fun mk_term t ctxt = 
        decon_cartouche_ast t |> Symbol_Pos.explode |> Token.read_cartouche |>
        (fn t => Args.term (Context.Proof ctxt,[t]) |> #1)

      val mk_pre = mk_term tpre 
      val mk_post = mk_term tpost
        
      fun mk_prog ctxt = decon_cartouche_ast tprog |> IMP_Parser.parse_command_at ctxt 
    
      val (_,res) = gen_make_htriple ctxt total mk_pre mk_prog mk_post      
    in 
      res
    end
    | htriple_tr _ _ args = raise TERM ("htriple_tr", args)
      
    
  end
\<close>
  
parse_translation \<open>[
  (@{syntax_const "_Htriple"}, VCG_Htriple_Syntax.htriple_tr true),
  (@{syntax_const "_Htriple_Partial"}, VCG_Htriple_Syntax.htriple_tr false)
  ]
\<close>
   

term \<open>\<^htriple_partial> \<open>n\<ge>0+x+notex\<close> \<open>while (n\<noteq>0) n = n - 1; x=x+1\<close> \<open>n=0 \<and> x=1+x\<^sub>0\<close>\<close> 
term \<open>\<^htriple> \<open>n\<ge>0+x+notex\<close> \<open>while (n\<noteq>0) n = n - 1; x=x+1\<close> \<open>n=0 \<and> x=1+x\<^sub>0\<close>\<close>


subsubsection \<open>Program Specification Commands\<close>
ML \<open>
  structure VCG_Program_Spec = struct
  
    structure PPData = Generic_Data (
      type T = (Proof.context -> conv) option
      val empty = NONE
      val extend = I
      val merge = merge_options
    )

    fun set_postprocessor pp = PPData.map (K (SOME pp)) 
    val get_postprocessor = PPData.get o Context.Proof
  
  
    fun define_program binding cmd lthy = let
      val lhs = Free (Binding.name_of binding, fastype_of cmd)
      val eqn = Logic.mk_equals (lhs,cmd)
      
      val ((lhs,(_,def_thm)),lthy) = Specification.definition (SOME (binding,NONE,Mixfix.NoSyn)) [] [] ((Binding.empty,[]),eqn) lthy
    in 
      ((lhs,def_thm),lthy)
    end 
  
    fun define_program_cmd binding cmd_src lthy = let
      val cmd = IMP_Parser.parse_command_at lthy cmd_src
      val cmd = if Term_Annot.has_annotations cmd then 
          (warning "Stripped annotations from program"; Term_Annot.strip_annotated_terms cmd) 
        else cmd

      val (_,lthy) = define_program binding cmd lthy
    in 
      lthy
    
    end 

    fun spec_program_cmd partial bnd pre_src post_src cmd_src lthy = let
      val total = not partial
      
      fun mk_cmd ctxt = IMP_Parser.parse_command_at ctxt cmd_src
      fun mk_pre ctxt = Syntax.read_term ctxt pre_src
      fun mk_post ctxt = Syntax.read_term ctxt post_src
      
      val (stripped_cmd,goal) = VCG_Htriple_Syntax.gen_make_htriple lthy total mk_pre mk_cmd mk_post
      
      val goal = HOLogic.mk_Trueprop goal

      (* Define command *)
      val ((cmd_const,def_thm),lthy) = define_program bnd stripped_cmd lthy
      
      val pos = Position.thread_data ();
        
      fun after_qed thmss lthy = let
      
        val raw_thms = flat thmss
        
        
        (* Strip annotations from the proved theorem *)
        val thms = map (VCG_Htriple_Syntax.strip_annotations lthy) raw_thms
          
        (* Unfold to standard Hoare-triple syntax, getting rid of the s0 abstraction in program *)
        val thms = map (Local_Defs.unfold lthy @{thms HT'_unfolds}) thms
                
        (* Postprocess theorem *)
        val thms = case get_postprocessor lthy of
          NONE => thms
        | SOME pp => map (Conv.fconv_rule (pp lthy)) thms 
        
        (* Fold definition in theorem *)
        val thms = map (Local_Defs.fold lthy [def_thm]) thms
        
        (* Sanity check: Has definition actually been folded? *)
        val _ = forall (exists_subterm (curry op = cmd_const) o Thm.prop_of) thms
          orelse raise THM("spec_program_cmd: Failed to fold command definition",~1,thms)
        
        val (_,lthy) = Local_Theory.note ((Binding.suffix_name "_raw_spec" bnd,[]),raw_thms) lthy
        val ((res_name,res),lthy) = Local_Theory.note ((Binding.suffix_name "_spec" bnd,[]),thms) lthy
        
        (* TODO/FIXME: Defined constant still shown as free variable in output here. *)
        val _ = Proof_Display.print_results true pos lthy ((Thm.theoremK,res_name),[("",res)]);
        
      in
        lthy
      end
    
    in Proof.theorem NONE after_qed [[(goal,[])]] lthy end
    
  
  end

\<close>


ML \<open>
  Outer_Syntax.local_theory \<^command_keyword>\<open>program_def\<close> "IMP program definition"
    (Parse.binding --| @{keyword "="} -- (Parse.position (Parse.cartouche>>cartouche)) 
    >> (fn (binding,cmd_src) => VCG_Program_Spec.define_program_cmd binding cmd_src ))

\<close>

ML \<open>
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>program_spec\<close> "Define IMP program and prove specification"
    ((Args.mode "partial" -- Parse.binding 
      --| \<^keyword>\<open>assumes\<close> -- Parse.term 
      --| \<^keyword>\<open>ensures\<close> -- Parse.term 
      --| \<^keyword>\<open>defines\<close> -- (Parse.position (Parse.cartouche>>cartouche)) 
      ) >> (fn ((((partial,bnd),pre_src),post_src),cmd_src) => VCG_Program_Spec.spec_program_cmd partial bnd pre_src post_src cmd_src))

\<close>


subsection \<open>Ad-Hoc Regression Tests\<close>

experiment
begin

program_def p1 = \<open>n = n + 1\<close>

program_spec (partial) p2
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @invariant \<open>n\<ge>0\<close> { if n+1>1 then n=n-1 }\<close>
  oops

program_spec p2'
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @variant \<open>nat n\<close> @invariant \<open>n\<ge>0\<close> { n=n-1 }\<close>
  oops


end

end
