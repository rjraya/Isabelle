theory Wellfounded_Demo
imports Main
begin

  text \<open>A relation is well-founded, if every non-empty set has a minimal element.
    Note that we use 'minimal' here, despite \<open>R\<close> needs not to be an ordering relation. \<close>
  definition "mywf R \<equiv> \<forall>A. A\<noteq>{} \<longrightarrow> (\<exists>m\<in>A. \<forall>x\<in>A. \<not>(x,m)\<in>R)"

  text \<open>Often, it makes sense to define elim and intro rules. 
    This will make the definition easier to use, in particular
    if quantifiers are involved.\<close>
    
  lemma mywfI: 
    assumes "\<And>A. A\<noteq>{} \<Longrightarrow> \<exists>m\<in>A. \<forall>x\<in>A. \<not>(x,m)\<in>R"
    shows "mywf R"
    using assms unfolding mywf_def by auto
    
  lemma mywfE: 
    assumes "mywf R"
    assumes "A\<noteq>{}"
    obtains m where "m\<in>A" "\<forall>x\<in>A. \<not>(x,m)\<in>R"
    using assms unfolding mywf_def by auto

  text \<open>Well-founded induction\<close>
  lemma mywf_induction:
    assumes WF: "mywf R"
    assumes STEP: "\<And>x. (\<forall>y. (y,x)\<in>R \<longrightarrow> P y) \<Longrightarrow> P x"
    shows "P x"
  proof (rule ccontr)  
    assume \<open>\<not>P x\<close>
    let ?S = "{x. \<not>P x}"    
    (* the parser removes the ?S so the isar core doesn't know about it *)
    obtain m where "m \<in> ?S" "\<forall> x. (x,m) \<notin> R" 
      apply(rule mywfE[OF WF])
    (* Hint: what do you know about least element in ?S ? *)
   
    oops    
    
  text \<open>Sample proof that @{term \<open>(<)\<close>} on @{typ \<open>nat\<close>} is well-founded: \<close>
    
  lemma "mywf {(x::nat,y). x<y}"
  proof (rule mywfI, clarsimp)
    thm nat_less_induct \<comment> \<open>Fortunately, complete induction is already there for @{typ \<open>nat\<close>}!\<close>
  
    fix A :: "nat set"
    assume "A\<noteq>{}"
    then obtain n where "n\<in>A" by auto
    thus "\<exists>m\<in>A. \<forall>x\<in>A. \<not>x<m" by (induction n rule: nat_less_induct) auto
  qed

  
  text \<open>Of course, Isabelle/HOL's standard library defines the concept of well-foundedness already!\<close>  
  lemma mywf_is_wf: "mywf R \<longleftrightarrow> wf R"
    unfolding mywf_def 
    apply rule
    subgoal by (metis empty_iff wfI_min)
    subgoal by (metis wfE_min')
    done
  
  text \<open>So we will use @{const \<open>wf\<close>}. (Better reuse than reinvent)\<close>

  thm wf_induct 
  thm wf_induct_rule  \<comment> \<open>This version is easier to use for proofs! \<close>
  (* proof rules will be more useful when formulated in the meta-level *)
    
  text \<open>The set-version of @{term "(<)"}\<close>
  term less_than
  thm less_than_iff
  thm wf_less_than
  
  
  text \<open>The measure wrt. a function @{term_type \<open>f :: 'a \<Rightarrow> nat\<close>} relates \<open>a,b\<close> iff @{prop \<open>f a < f b\<close>}\<close>
  term measure
  thm in_measure
  
  text \<open>Obviously, measures are well-founded!\<close>
  thm wf_measure
  

  function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where
      "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
    by pat_completeness auto  
  
  termination
    apply (relation "measure (\<lambda>(i,N). f i N)")  (* Can you provide a suitable measure? *)
    apply auto
    oops
    
  
end
