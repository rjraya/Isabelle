theory Defs
  imports "IMP2.VCG"
begin

lemma intvs_singleton[simp]: 
  "{i::int..<i + 1} = {i}" 
  "{i-1..<i::int} = {i-1}" 
  by auto

lemma intvs_incr_h:
  "l\<le>h \<Longrightarrow> {l::int..<h + 1} = insert h {l..<h}"
  by auto

lemma intvs_decr_h:
  "{l::int..<h - 1} = {l..<h} - {h-1}"
  by auto
  
lemma intvs_incr_l:
  "{l+1..<h::int} = {l..<h} - {l}"
  by auto

lemma intvs_decr_l:
  "l\<le>h \<Longrightarrow> {l-1..<h::int} = insert (l-1) {l..<h}"
  by auto
  
lemmas intvs_incdec = intvs_incr_h intvs_incr_l intvs_decr_h intvs_decr_l

lemma intvs_lower_incr: "l<h \<Longrightarrow> {l::int..<h} = insert l ({l+1..<h})" by auto
lemma intvs_upper_decr: "l<h \<Longrightarrow> {l::int..<h} = insert (h-1) ({l..<h-1})" by auto


definition "is_equil a l h i \<equiv> l\<le>i \<and> i<h \<and> (\<Sum>j=l..<i. a j) = (\<Sum>j=i..<h. a j)"

end