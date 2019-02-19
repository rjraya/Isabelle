theory Hw14
  imports Main
begin

thm Union_upper Union_least
theorem postfix_step: 
  assumes MONO: "\<And>x y. x\<subseteq>y \<Longrightarrow> f x \<subseteq> f y"  
  assumes POST: "x\<^sub>0 \<subseteq> f x\<^sub>0" 
  shows "\<Union> {(f^^i)(x\<^sub>0)| i::nat. True} \<subseteq> \<Union> {(f^^(Suc i))(x\<^sub>0)| i :: nat. True}" 
  (is "\<Union> ?C \<subseteq> \<Union> ?D")
proof -
  have "(\<And>X. X \<in> {(f ^^ i) x\<^sub>0 |i. True} \<Longrightarrow> X \<subseteq> \<Union>{(f ^^ Suc i) x\<^sub>0 |i. True})"
  proof -
    fix X
    assume "X \<in> {(f ^^ i) x\<^sub>0 |i. True}"
    then obtain i where i_form: "X = (f ^^ i) x\<^sub>0" by auto
    then show "X \<subseteq> \<Union>{(f ^^ Suc i) x\<^sub>0 |i. True}"
    proof(cases i)
      case 0
      from i_form 0 have "X = x\<^sub>0" by auto
      from this POST have t1: "X \<subseteq> x\<^sub>0" by simp
      have "f(x\<^sub>0) = (f ^^ Suc 0) x\<^sub>0" by simp
      then have "f(x\<^sub>0) \<in> {(f ^^ Suc i) x\<^sub>0 |i. True}" by blast
      from this Union_upper[of "f(x\<^sub>0)" "{(f ^^ Suc i) x\<^sub>0 |i. True}"] 
      have t2: "f x\<^sub>0 \<subseteq> \<Union>{(f ^^ Suc i) x\<^sub>0 |i. True}" by auto
      from t1 t2 POST show ?thesis by simp
    next
      case (Suc j)
      from this i_form have "X = (f ^^ Suc j) x\<^sub>0" by simp
      then show ?thesis by blast
    qed
  qed

  from this Union_least[of ?C "\<Union> ?D"] show ?thesis by blast
qed

context 
  fixes f :: "'a set \<Rightarrow> 'a set"
  assumes continuous: "\<And> X. X \<noteq> {} \<Longrightarrow> f (\<Union> X) = \<Union> (f ` X)"
begin

theorem mono: 
  assumes inc: "x \<subseteq> y"
  shows "f x \<subseteq> f y"
proof -
  from continuous[of "{x,y}"] have rewrite: "f (x \<union> y) = f(x) \<union> f(y)" by auto
  from this inc have "x \<union> y = y" by auto
  from this have 1: "f(x \<union> y) = f(y)" by simp
  from rewrite have 2: "f(x) \<subseteq> f(x \<union> y)" by simp
  from 1 2 show "f(x) \<subseteq> f(y)" by simp
qed

lemma lfp_fold: "f (lfp f) = lfp f" 
  using lfp_unfold mono unfolding mono_def by auto

theorem lfp_ge: "\<Union> {(f^^i){} | i. True} \<subseteq> lfp f"
proof -
  have "\<And> i. (f^^i){} \<subseteq> lfp f" 
  proof -
    fix i
    show "(f^^i){} \<subseteq> lfp f"
    proof(induction i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then have 0: "(f^^(Suc i)) {} = f((f^^(i)){})" by simp
      from this mono[of "(f^^(i)){}" "lfp f"] Suc.IH have 1: "... \<subseteq> f(lfp f)" by simp
      from this lfp_fold have 2: "... = lfp f" by simp
      from 0 1 2 show ?case by simp
    qed
  qed

  from this Union_least[of "{(f^^i){} | i. True}" "lfp(f)"] 
  show ?thesis by blast
qed

theorem lfp_le: "lfp f \<subseteq> \<Union> {(f^^i){}|i. True}" (is "_ \<subseteq> \<Union> ?S")
proof -
  have "(f^^0) {} = {}" by simp
  from continuous[of ?S] 
  have 0: "f (\<Union>{(f ^^ i) {} |i. True}) = UNION {(f ^^ i) {} |i. True} f" by blast
  then have 1: "... =  \<Union> {(f ^^ (i+1)) {} |i. True}" by auto
  then have 2: "... = ((f^^0) {}) \<union> (\<Union> {(f ^^ (i+1)) {} |i. True})" by simp
  then have 3: "... = \<Union> {(f ^^ (i+1)) {} |i. True}" by simp
  from 0 1 2 3 have 4: "f (\<Union>{(f ^^ i) {} |i. True}) = \<Union> {(f ^^ (i+1)) {} |i. True}" by simp
  have lower: "lfp f \<subseteq> x" if "f x \<subseteq> x" for x using that unfolding lfp_def by auto
  from lower[of "\<Union>{(f ^^ i) {} |i. True}"] 4 show " lfp f \<subseteq> \<Union>{(f ^^ i) {} |i. True}" by blast
qed

corollary 
 "lfp f = \<Union> {(f^^i) {}|i. True}" using lfp_le lfp_ge ..
end

end