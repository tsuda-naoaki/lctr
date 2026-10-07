theory Core_Continuum_Boundary_Alignment
  imports LCTR_Core_Continuum_Boundary.Core_Continuum_Boundary
begin
lemmas margin_nonneg = Core_Continuum_Boundary.margin_nonneg
lemmas margin_zero = Core_Continuum_Boundary.margin_zero
lemmas margin_negative = Core_Continuum_Boundary.margin_negative
lemmas margin_positive = Core_Continuum_Boundary.margin_positive
lemmas excess_nonneg = Core_Continuum_Boundary.excess_nonneg
lemmas excess_zero = Core_Continuum_Boundary.excess_zero
lemmas excess_positive = Core_Continuum_Boundary.excess_positive
lemmas validity_characterizations = nonnegative_family.validity_characterizations
lemmas saturation_excess_disjoint = nonnegative_family.saturation_excess_disjoint
lemmas valid_not_robust = nonnegative_family.valid_not_robust
lemmas subset_saturation = nonnegative_family.subset_saturation
lemmas subset_excess = nonnegative_family.subset_excess
lemmas maximal_initial_greatest = Core_Continuum_Boundary.maximal_initial_greatest
lemmas maximal_initial_eq = Core_Continuum_Boundary.maximal_initial_eq
lemmas monotone_defects_initial = Core_Continuum_Boundary.monotone_defects_initial
lemmas initial_boundary = Core_Continuum_Boundary.initial_boundary

lemma least_subset:
  fixes a b :: "'a::preorder"
  assumes sub: "S\<subseteq>T" and a: "a\<in>S \<and> (\<forall>x\<in>S. a\<le>x)"
    and b: "b\<in>T \<and> (\<forall>x\<in>T. b\<le>x)"
  shows "b\<le>a"
  using sub a b by blast

lemmas maximal_effective_interval = Core_Continuum_Boundary.maximal_effective_interval
lemmas first_excess = nonnegative_scale_family.first_excess

lemma maximum_has_no_excess:
  fixes d :: "'a::preorder\<Rightarrow>'i\<Rightarrow>ereal"
  assumes member: "a\<in>maximal_initial {x. valid J (d x) e}"
    and dn: "\<And>i. i\<in>J \<Longrightarrow> 0\<le>d a i"
    and en: "\<And>i. i\<in>J \<Longrightarrow> 0\<le>e i"
  shows "exceeded J (d a) e={}"
proof -
  have subset: "maximal_initial {x. valid J (d x) e} \<subseteq> {x. valid J (d x) e}"
    using maximal_initial_greatest[where V="{x. valid J (d x) e}"]
    unfolding initial_family_def by blast
  have valid: "valid J (d a) e" using subset member by blast
  interpret F: nonnegative_family J "d a" e
    by standard (fact dn, fact en)
  show ?thesis using valid F.validity_characterizations by blast
qed

lemmas infinite_saturation_control = Core_Continuum_Boundary.infinite_saturation_control
lemmas no_least_open_excess_control = Core_Continuum_Boundary.no_least_open_excess_control

lemma first_excess_is_least:
  fixes d :: "'a::linorder\<Rightarrow>'i\<Rightarrow>ereal"
  assumes dn: "\<And>x i. i\<in>J \<Longrightarrow> 0\<le>d x i"
    and en: "\<And>i. i\<in>J \<Longrightarrow> 0\<le>e i"
    and b: "least_in {x. \<not>valid J (d x) e} b"
  shows "least_in {x. exceeded J (d x) e\<noteq>{}} b"
proof -
  have all: "\<And>x. valid J (d x) e = (exceeded J (d x) e={})"
  proof -
    fix x
    interpret F: nonnegative_family J "d x" e
      by standard (fact dn, fact en)
    show "valid J (d x) e = (exceeded J (d x) e={})"
      using F.validity_characterizations by blast
  qed
  show ?thesis using b by (simp only: all)
qed

ML \<open>
val roots = @{thms margin_nonneg margin_zero margin_negative margin_positive
  excess_nonneg excess_zero excess_positive validity_characterizations saturation_excess_disjoint
  valid_not_robust subset_saturation subset_excess maximal_initial_greatest maximal_initial_eq
  monotone_defects_initial initial_boundary least_subset maximal_effective_interval first_excess
  maximum_has_no_excess infinite_saturation_control no_least_open_excess_control first_excess_is_least};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
