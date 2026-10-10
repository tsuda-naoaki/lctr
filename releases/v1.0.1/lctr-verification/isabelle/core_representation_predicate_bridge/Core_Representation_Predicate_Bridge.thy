theory Core_Representation_Predicate_Bridge
 imports Main
begin

definition eq_kernel where "eq_kernel A f = {(x,y). x\<in>A \<and> y\<in>A \<and> f x=f y}"
definition relation_pullback where
 "relation_pullback A f lt = {(x,y). x\<in>A \<and> y\<in>A \<and> (f x,f y)\<in>lt}"
definition ord_rep_cond where
 "ord_rep_cond A f E R lt \<longleftrightarrow> eq_kernel A f=E \<and> relation_pullback A f lt=R"

lemma kernel_membership:
 "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> ((x,y)\<in>eq_kernel A f \<longleftrightarrow> f x=f y)"
 by (simp add: eq_kernel_def)

lemma kernel_equivalence: "equiv A (eq_kernel A f)"
 unfolding equiv_def refl_on_def sym_def trans_def eq_kernel_def by auto

lemma kernel_set_exact:
 assumes "E\<subseteq>A\<times>A"
 shows "eq_kernel A f=E \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. f x=f y \<longleftrightarrow> (x,y)\<in>E)"
 using assms unfolding eq_kernel_def by auto

lemma pullback_set_exact:
 assumes "R\<subseteq>A\<times>A"
 shows "relation_pullback A f lt=R \<longleftrightarrow>
  (\<forall>x\<in>A. \<forall>y\<in>A. (f x,f y)\<in>lt \<longleftrightarrow> (x,y)\<in>R)"
 using assms unfolding relation_pullback_def by auto

lemma representation_condition_exact:
 assumes e: "E\<subseteq>A\<times>A" and r: "R\<subseteq>A\<times>A"
 shows "ord_rep_cond A f E R lt \<longleftrightarrow>
  (\<forall>x\<in>A. \<forall>y\<in>A. f x=f y \<longleftrightarrow> (x,y)\<in>E) \<and>
  (\<forall>x\<in>A. \<forall>y\<in>A. (f x,f y)\<in>lt \<longleftrightarrow> (x,y)\<in>R)"
 by (simp only: ord_rep_cond_def kernel_set_exact[OF e] pullback_set_exact[OF r])

definition collapse :: "bool\<Rightarrow>nat" where "collapse x=0"
definition nat_strict :: "(nat\<times>nat)set" where "nat_strict={(x,y). x<y}"

lemma noninjective_control:
 "ord_rep_cond UNIV collapse UNIV {} nat_strict \<and>
  collapse False=collapse True \<and> False\<noteq>True"
 by (auto simp: ord_rep_cond_def eq_kernel_def relation_pullback_def collapse_def nat_strict_def)

lemma missing_order_control:
 "eq_kernel UNIV collapse=UNIV \<and>
  \<not>ord_rep_cond UNIV collapse UNIV {(False,True)} nat_strict"
 by (auto simp: ord_rep_cond_def eq_kernel_def relation_pullback_def collapse_def nat_strict_def)

lemma missing_kernel_control:
 "relation_pullback UNIV collapse nat_strict={} \<and>
  \<not>ord_rep_cond UNIV collapse {(x,y). x=y} {} nat_strict"
 unfolding ord_rep_cond_def eq_kernel_def relation_pullback_def collapse_def nat_strict_def
 by auto

ML \<open>
val roots = @{thms kernel_membership kernel_equivalence kernel_set_exact pullback_set_exact
 representation_condition_exact noninjective_control missing_order_control missing_kernel_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
