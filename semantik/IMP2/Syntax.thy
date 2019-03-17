section \<open>Syntax of IMP2\<close>
theory Syntax
imports Main
begin

subsection \<open>Syntax Types\<close>
  type_synonym vname = string
  type_synonym val = int
  
  datatype aexp = 
      N int 
    | V vname 
    | Unop "int \<Rightarrow> int" aexp 
    | Binop "int \<Rightarrow> int \<Rightarrow> int" aexp aexp
    
  datatype bexp = 
      Bc bool 
    | Not bexp 
    | BBinop "bool \<Rightarrow> bool \<Rightarrow> bool" bexp bexp 
    | Cmpop "int \<Rightarrow> int \<Rightarrow> bool" aexp aexp

  datatype
    com = SKIP 
        | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
        | Seq    com  com         ("_;;/ _"  [61, 60] 60)
        | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
        | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)

subsection \<open>Parser for IMP Programs\<close>

  text \<open>The parser also understands annotated programs.
    However, the basic parser will leave the annotations uninterpreted,
    and it's up to the client of the parser to interpret them.
  \<close>

  
  abbreviation (input) While_Annot :: "'a \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
    where "While_Annot I \<equiv> While"

  (* Note: Still a very early prototype *)

  abbreviation (input) VARIABLE :: "string \<Rightarrow> string" where "VARIABLE x \<equiv> x" (* Used to mark variables *)
  
  syntax "_annotated_term" :: "logic \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> logic" (* Annotated term: term string pos *)
  
  
  ML \<open>
    structure Term_Annot : sig
      (* Annotate terms *)
      val annotate_term: term -> string * Position.T -> term
      val dest_annotated_term: term -> (string * Position.T) * term
      
      (* Annotation = annotated dummy term *)
      val annotation: string * Position.T -> term
      val dest_annotation: term -> term

      (* Checking for annotations in Term *)
      val is_annotated_term: term -> bool
      val has_annotations: term -> bool

      (* Removing annotations *)
      val strip_annotations: term -> term
      (* Replaces annotated terms by dummy term *)
      val strip_annotated_terms: term -> term
            
      (* Parsing *)
      (* Parse cartouche (independent of term annotations)*)
      val parse_cartouche: (string * Position.T) parser
      (* Parse cartouche into annotation *)
      val parse_annotation: term parser
      (* Parse cartouche into annotation of syntax constant (used to get typed annotations) *)
      val parse_annotate: string -> term parser
      
      (* Read term from cartouche and position *)
      val read_term: Proof.context -> string * Position.T -> term
      
      (* Read annotation part of annotated term as term *)
      val read_annotation_as_term: Proof.context -> term -> term * term
    end = struct
      fun annotate_term t (str,pos) = let
        val pos = Free (Term_Position.encode pos,dummyT)
        val str = Free (str,dummyT)
        val c = Const (@{syntax_const "_annotated_term"}, dummyT --> dummyT --> dummyT --> dummyT)
      in
        c$t$str$pos
      end

      fun dest_annotated_term (Const (@{syntax_const "_annotated_term"},_)$t$Free (str,_)$Free (pos,_)) = let
            val pos = case Term_Position.decode pos of 
              SOME pos => pos | NONE => raise TERM ("dest_term_annot: invalid pos",[t])
          in ((str,pos),t) end
        | dest_annotated_term t = raise TERM("dest_annot",[t])      
        
      val is_annotated_term = can dest_annotated_term
      val has_annotations = Term.exists_subterm is_annotated_term

      val annotation = annotate_term Term.dummy
      val dest_annotation = dest_annotated_term #> #2
      
      val parse_cartouche = Parse.position Parse.cartouche >> apfst cartouche

      val parse_annotation = parse_cartouche >> annotation
      
      fun parse_annotate n = parse_cartouche >> annotate_term (Const (n,dummyT))
      
      
      fun read_term ctxt spos = let
        val tk = Symbol_Pos.explode spos |> Token.read_cartouche
      in
        Args.term (Context.Proof ctxt, [tk]) |> #1
      end  
      
      fun read_annotation_as_term ctxt = dest_annotated_term #>> read_term ctxt 
      
      
      (* Strip one level of term annotations. *)
      fun strip_annotations (Const (@{syntax_const "_annotated_term"},_)$t$_$_) = t
        | strip_annotations (a$b) = strip_annotations a $ strip_annotations b
        | strip_annotations (Abs (x,T,t)) = Abs (x,T,strip_annotations t)
        | strip_annotations t = t

        
      fun strip_annotated_terms (Const (@{syntax_const "_annotated_term"},_)$_$_$_) = Term.dummy
        | strip_annotated_terms (a$b) = strip_annotated_terms a $ strip_annotated_terms b
        | strip_annotated_terms (Abs (x,T,t)) = Abs (x,T,strip_annotated_terms t)
        | strip_annotated_terms t = t
              
    end    
  \<close>
    
  (* Syntax constants to discriminate annotation types *)
  syntax
    "_invariant_annotation" :: "_"
    "_variant_annotation" :: "_"
    "_relation_annotation" :: "_"
  
  
  ML \<open>
    structure IMP_Parser = struct
    
      fun scan_if_then_else scan1 scan2 scan3 xs = let
        val r = SOME (Scan.catch scan1 xs) handle Fail _ => NONE
      in
        case r of 
          NONE => scan3 xs
        | SOME (a,xs) => scan2 a xs
      end
      
    
      infixr 0 |||
      infix 5 ---
  
      fun (g,p) ||| e = scan_if_then_else g p e
          
      fun lastg (g,p) = g :|-- p
    
    
      datatype op_kind = Binop | Unop
      
      val int_c = @{const N}
      val bool_c = @{const Bc}
      val var_c = @{const V}
      
      
      type op_decl = op_kind * (string * term)

      fun name_eq_op_decl ((k,(a,_)), ((k',(b,_)))) = k=k' andalso a=b
      
      fun is_binop ((Binop,_):op_decl) = true | is_binop _ = false
      fun is_unop ((Unop,_):op_decl) = true | is_unop _ = false
      
      structure Opr_Data = Generic_Data (
        type T = op_decl list Inttab.table
        val empty = Inttab.empty
        val merge = Inttab.merge_list name_eq_op_decl
        val extend = I
      )
  
      fun tab_add_unop (p,n,f) = Inttab.insert_list name_eq_op_decl (p,(Unop,(n,f)))
      fun tab_add_binop (p,n,f) = Inttab.insert_list name_eq_op_decl (p,(Binop,(n,f)))
      
      val add_unop = Opr_Data.map o tab_add_unop
      val add_binop = Opr_Data.map o tab_add_binop

            
      fun mk_variable t = Const (@{const_abbrev VARIABLE}, dummyT)$t
      val parse_varname = (Parse.short_ident) 
        >> HOLogic.mk_string >> mk_variable 
      
      local
        fun parse_level parse_opr op_decls = let
        
          val binops = filter is_binop op_decls |> 
            map (fn (_,(k,c)) => Parse.$$$ k >> (K c))
          
          val unops = filter is_unop op_decls |>
            map (fn (_,(k,c)) => Parse.$$$ k >> (K c))
          
          val bopg = Parse.group (fn () => "Binary operator") (Scan.first binops) 
          val uopg = Parse.group (fn () => "Unary operator") (Scan.first unops) 
            
          
          fun mk_right a ([]) = a
            | mk_right a (((f,b)::fxs)) = mk_right (f$a$b) fxs
          
          val parse_bop = (parse_opr, fn a => Scan.repeat (bopg -- parse_opr) >> mk_right a)
          val parse_unop = (uopg, fn f => parse_opr >> (fn x => f$x))  
          
          val parse = (parse_bop ||| lastg parse_unop)
        in
          parse
        end
        
        fun parse_levels lvls = let
          val parse_int = Parse.nat >> HOLogic.mk_number @{typ int} >> (fn t => int_c$t)
          val parse_var = parse_varname >> (fn t => var_c$t)
          val parse_bool = 
               Parse.$$$ "true" >> (K (bool_c $ @{term True}))
            || Parse.$$$ "false" >> (K (bool_c $ @{term False}))
        
          fun parse [] xs = (parse_int || parse_var || parse_bool || (@{keyword "("} |-- parse lvls --| @{keyword ")"})) xs
            | parse (lv::lvs) xs = (parse_level (parse lvs) lv) xs
        
        in
          parse lvls
        end
        
      in      
        val parse_exp_tab = Inttab.dest #> map snd #> parse_levels
        
        val parse_exp = Context.Proof #> Opr_Data.get #> parse_exp_tab
      end  

      
      val fixed_keywords = ["(",")","{","}","true","false","if","then","else","while","scope","skip","=",";",
        "@invariant", "@variant", "@relation",
        "__term"]
      
      fun parse_command ctxt = let
      
        val g_parse_assign = 
          (parse_varname, fn x => Parse.$$$ "=" |-- parse_exp ctxt >> (fn t => @{term Assign}$x$t))
          
        val g_parse_skip = (Parse.$$$ "skip", fn _ => Scan.succeed @{term SKIP})
        
        fun g_parse_block p = (Parse.$$$ "{", fn _ => p --| Parse.$$$ "}")

        val pkw = Parse.keyword_markup (true,Markup.keyword1)
        
        val parse_invar_annotation = (pkw "@invariant", fn _ => Term_Annot.parse_annotate @{syntax_const "_invariant_annotation"})
        val parse_var_annotation = (pkw "@variant", fn _ => Term_Annot.parse_annotate @{syntax_const "_variant_annotation"})
        val parse_rel_annotation = (pkw "@relation", fn _ => Term_Annot.parse_annotate @{syntax_const "_relation_annotation"})

        val parse_while_annots = Scan.repeat (parse_invar_annotation ||| parse_var_annotation ||| lastg parse_rel_annotation)
              >> HOLogic.mk_tuple
        
        val While_Annot_c = Const (@{const_abbrev While_Annot}, dummyT --> @{typ "bexp \<Rightarrow> com \<Rightarrow> com"})
        
        fun parse_atomic_com xs = 
          (g_parse_assign ||| g_parse_skip ||| lastg (g_parse_block parse_com)) xs
        
        and parse_com1 xs = (
            (pkw "if", fn _ => parse_exp ctxt --| pkw "then" -- parse_com1 
              -- scan_if_then_else (pkw "else") (K parse_com1) (Scan.succeed @{term "SKIP"}) 
                >> (fn ((b,t),e) => @{term "If"}$b$t$e))
         ||| (pkw "while", fn _ => pkw "(" |-- parse_exp ctxt --| pkw ")" -- parse_while_annots -- parse_com1
                >> (fn ((b,annots),c) => While_Annot_c$annots$b$c))
         ||| (pkw "__term", fn _ => Term_Annot.parse_cartouche >> Term_Annot.read_term ctxt)
         ||| parse_atomic_com
        
        ) xs
        and parse_com xs = (
           parse_com1 -- (Scan.unless (Parse.$$$ ";") (Scan.succeed NONE) || Parse.$$$ ";" |-- parse_com >> SOME )
           >> (fn (s,SOME t) => @{term "Seq"}$s$t | (s,NONE) => s)
        
        ) xs
      
      in parse_com end 
      
      fun parse_all ctxt p src = let
        val src = map Token.init_assignable src
        val (res,_) = Scan.catch (Scan.finite Token.stopper (p --| Scan.ahead Parse.eof)) src
        
        val rp = map Token.reports_of_value src |> flat
        val _ = Context_Position.reports ctxt rp
        
        (* val src = map Token.closure src |> @{print} *)
      in
        res
      end
      
      val keywords_of_tab : op_decl list Inttab.table -> string list 
        = Inttab.dest_list #> map (snd#>snd#>fst)
      
      fun keywords ctxt = let 
        val kws = ctxt |> Context.Proof |> Opr_Data.get |> keywords_of_tab 
        val kws = (kws @ fixed_keywords)
          |> Symtab.make_set |> Symtab.keys
          |> map (fn x => ((x,Position.none),Keyword.no_spec))
      in
        Keyword.add_keywords kws Keyword.empty_keywords
      end
        
      fun parse_pos_text p ctxt (pos,text) = 
          Token.explode (keywords ctxt) pos text 
        |> filter Token.is_proper  
        |> parse_all ctxt (p ctxt)
        
      fun parse_sympos p ctxt xs = let
        val kws = keywords ctxt
        val tks = Token.tokenize kws {strict=true} xs
        val rp = map (Token.reports kws) tks |> flat  (* TODO: More detailed report AFTER parsing! *)
        val _ = Context_Position.reports_text ctxt rp
      in
          tks 
        |> filter Token.is_proper  
        |> parse_all ctxt (p ctxt)
      end

      fun variables_of t = let
        fun add (Const (@{const_abbrev VARIABLE},_)$x) = Symtab.insert_set (HOLogic.dest_string x)
          | add (a$b) = add a #> add b
          | add (Abs (_,_,t)) = add t
          | add _ = I
      
      in
        add t Symtab.empty |> Symtab.keys
      end

      
      fun parse_command_at ctxt spos = let
        val syms = spos |> Symbol_Pos.explode |> Symbol_Pos.cartouche_content
        val res = parse_sympos parse_command ctxt syms
      in
        res
      end

      fun cartouche_tr ctxt args = let  
        fun err () = raise TERM ("imp",args)
      
        fun parse spos = let 
          val t = parse_command_at ctxt spos 
          val t = if Term_Annot.has_annotations t then (warning "Stripped annotations from program"; Term_Annot.strip_annotated_terms t) else t
          
        in  
          t
        end
        
      in 
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ parse (s,pos) $ p
            | NONE => err ())
        | _ => err ())
      end
                
    end
  \<close>

  
  
  syntax "_Imp" :: "cartouche_position \<Rightarrow> logic" ("\<^imp>_")

  parse_translation \<open>
    [(@{syntax_const "_Imp"}, IMP_Parser.cartouche_tr)]
  \<close>

  term \<open>\<^imp>\<open>skip\<close>\<close>
  
  
  
    
  declaration \<open>K ( I
  #> IMP_Parser.add_unop (31,"-",@{term "Unop uminus"})  
  #> IMP_Parser.add_binop (25,"*",@{term "Binop ( *)"})
  #> IMP_Parser.add_binop (25,"/",@{term "Binop (div)"})
  #> IMP_Parser.add_binop (21,"+",@{term "Binop (+)"})
  #> IMP_Parser.add_binop (21,"-",@{term "Binop (-)"})
  #> IMP_Parser.add_binop (11,"<",@{term "Cmpop (<)"})
  #> IMP_Parser.add_binop (11,"\<le>",@{term "Cmpop (\<le>)"})
  #> IMP_Parser.add_binop (11,">",@{term "Cmpop (>)"})
  #> IMP_Parser.add_binop (11,"\<ge>",@{term "Cmpop (\<ge>)"})
  #> IMP_Parser.add_binop (11,"==",@{term "Cmpop (=)"})
  #> IMP_Parser.add_binop (11,"\<noteq>",@{term "Cmpop (\<noteq>)"})
  #> IMP_Parser.add_unop (7,"\<not>",@{term "Not"})
  #> IMP_Parser.add_binop (5,"\<and>",@{term "BBinop (\<and>)"})
  #> IMP_Parser.add_binop (3,"\<or>",@{term "BBinop (\<or>)"})
    )\<close>

subsection \<open>Examples\<close>
    
  term  \<open> \<^imp>\<open>
    a = 1;
    if true then a=a;
    if false then skip else {skip; skip};
    while (n > 0) 
      @invariant \<open>not interpreted here\<close>
      @variant \<open>not interpreted here\<close>
      @relation \<open>not interpreted here\<close>
    {
      a = a + a;
      
      __term \<open>IF Bc True THEN SKIP ELSE SKIP\<close>;
      
      n = n - 1
    }
  \<close>\<close>  
   
   
end
