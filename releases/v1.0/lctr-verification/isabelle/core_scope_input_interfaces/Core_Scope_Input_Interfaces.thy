theory Core_Scope_Input_Interfaces
 imports Main
begin

definition restrict_relation where "restrict_relation r A = r \<inter> (A \<times> A)"

lemma restriction_membership:
 "(x,y)\<in>restrict_relation r A \<longleftrightarrow> (x,y)\<in>r \<and> x\<in>A \<and> y\<in>A"
 by (simp add: restrict_relation_def)

lemma restriction_subtype:
 "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow>
  ((x,y)\<in>restrict_relation r A \<longleftrightarrow> (x,y)\<in>r)"
 by (simp add: restrict_relation_def)

lemma support_selection:
 "(\<forall>i\<in>I. \<exists>c\<in>C. supports i c) \<longleftrightarrow>
  (\<exists>f. \<forall>i\<in>I. f i\<in>C \<and> supports i (f i))"
proof
 assume h: "\<forall>i\<in>I. \<exists>c\<in>C. supports i c"
 define f where "f i = (SOME c. c\<in>C \<and> supports i c)" for i
 have hf: "\<And>i. i\<in>I \<Longrightarrow> f i\<in>C \<and> supports i (f i)"
  unfolding f_def by (rule someI_ex) (use h in blast)
 show "\<exists>f. \<forall>i\<in>I. f i\<in>C \<and> supports i (f i)"
  using hf by blast
next
 assume "\<exists>f. \<forall>i\<in>I. f i\<in>C \<and> supports i (f i)"
 then show "\<forall>i\<in>I. \<exists>c\<in>C. supports i c" by blast
qed

lemma shared_carrier_distinct_sources:
 "\<exists>carrier::bool\<Rightarrow>unit. carrier False=carrier True \<and>
  (False,0::nat)\<noteq>(True,0::nat)"
 by simp

ML \<open>
val roots = @{thms restriction_membership restriction_subtype support_selection shared_carrier_distinct_sources};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>

end
