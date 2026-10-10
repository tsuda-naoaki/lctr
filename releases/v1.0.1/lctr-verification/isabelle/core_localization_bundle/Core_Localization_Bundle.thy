theory Core_Localization_Bundle
  imports LCTR_Core_Failure_Multiplicity.Core_Failure_Multiplicity
    LCTR_Core_Series_Validity.Core_Series_Validity
    LCTR_Core_Structural_Burden.Core_Structural_Burden
begin

definition strict_domain where "strict_domain q={l. strict_complete (q l)}"
definition approx_domain where "approx_domain q={l. approx_complete (q l)}"
definition full_domain where "full_domain q={l. full (q l)}"

lemma domain_intersection: "full_domain q=strict_domain q\<inter>approx_domain q"
  by (auto simp: strict_domain_def approx_domain_def full_domain_def completion_split)

definition boundary_tokens :: "'a::linorder set\<Rightarrow>('a\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>token set" where
  "boundary_tokens V b = image (\<lambda>i. (3,i)) (boundary_support V b)"
definition lifted_burden where
  "lifted_burden F = nativeBurden (image abs_token (F\<inter>tokens))"

lemma carrier_exact:
  "tokens={(s,i). s<6 \<and> 1\<le>i \<and> i\<le>Core_Structural_Burden.count s}"
  by (simp add: tokens_def Core_Finite_Audit.count_def Core_Structural_Burden.count_def)

lemma lift_rep_exact:
  "t\<in>tokens \<Longrightarrow> rep_token (abs_token t)=t"
  by (rule abs_token_inverse) (simp only: carrier_exact[symmetric])

lemma edge_lift_exact:
  assumes a: "a\<in>tokens" and b: "b\<in>tokens"
  shows "Core_Structural_Burden.edge (abs_token a) (abs_token b)=Core_Finite_Audit.edge a b"
  by (simp add: Core_Structural_Burden.edge_def Core_Finite_Audit.edge_def
    lift_rep_exact[OF a] lift_rep_exact[OF b]
    Core_Structural_Burden.within_def Core_Finite_Audit.within_def)

lemma boundary_tokens_only_approx:
  "t\<in>boundary_tokens V b \<Longrightarrow> fst t=3"
  by (auto simp: boundary_tokens_def)

lemma boundary_tokens_typed: "boundary_tokens V b\<subseteq>tokens"
  by (auto simp: boundary_tokens_def boundary_support_def approximation_indices_def
    tokens_def Core_Finite_Audit.count_def)

lemma boundary_tokens_at_least:
  "least_outside V l \<Longrightarrow>
    boundary_tokens V b={(3,i) |i. i\<in>approximation_indices \<and> b l i}"
  by (auto simp: boundary_tokens_def support_at_boundary signature_support_def)

lemma no_boundary_no_tokens:
  "boundary_data V b={} \<Longrightarrow> boundary_tokens V b={}"
  by (simp add: boundary_empty_iff boundary_tokens_def no_boundary_no_support)

lemma no_boundary_no_burden:
  "boundary_data V b={} \<Longrightarrow> lifted_burden (boundary_tokens V b)={}"
  by (simp add: no_boundary_no_tokens lifted_burden_def nativeBurden_def burden_def)

record 'a localization_data =
  strict_validity :: "'a set"
  approx_validity :: "'a set"
  full_validity :: "'a set"
  max_interval :: "'a set"
  first_failure :: "token set \<times> (token\<Rightarrow>bool) \<times> ('a\<times>(nat\<Rightarrow>bool)) set"
  multiplicity :: "structural_class \<times> boundary_class"
  structural_burden :: "structural_token set \<times> structural_token set"
  six_signature_output :: "token\<Rightarrow>bool"

definition assemble :: "('a::linorder\<Rightarrow>token\<Rightarrow>internal_state)
  \<Rightarrow>('a\<Rightarrow>nat\<Rightarrow>bool)\<Rightarrow>'a\<Rightarrow>'a localization_data" where
  "assemble q b l = \<lparr>strict_validity=strict_domain q,
    approx_validity=approx_domain q, full_validity=full_domain q,
    max_interval=maximal_initial (approx_domain q),
    first_failure=Core_First_Failure_Report.report (q l) (approx_domain q) (masked_signature b),
    multiplicity=multiplicity_report (q l) (approx_domain q) b,
    structural_burden=(lifted_burden (failed_set (q l)),lifted_burden (boundary_tokens (approx_domain q) b)),
    six_signature_output=six_signature (q l)\<rparr>"

lemma assembled_domain_intersection:
  "full_validity (assemble q b l)=strict_validity (assemble q b l)\<inter>approx_validity (assemble q b l)"
  by (simp add: assemble_def domain_intersection)

lemma interval_within_approx:
  "max_interval (assemble q b l)\<subseteq>approx_validity (assemble q b l)"
  using maximal_initial_greatest[of "approx_domain q"]
  by (simp add: assemble_def initial_family_def)

lemma interval_equals_initial_approx:
  "initial (approx_domain q) \<Longrightarrow>
    max_interval (assemble q b l)=approx_validity (assemble q b l)"
  by (simp add: assemble_def maximal_initial_eq)

lemma quantitative_interval:
  fixes d :: "'a::linorder\<Rightarrow>nat\<Rightarrow>ereal"
  assumes bridge: "\<And>x. approx_complete (q x)=valid approximation_indices (d x) e"
    and mono: "\<And>i x y. i\<in>approximation_indices \<Longrightarrow> x\<le>y \<Longrightarrow> d x i\<le>d y i"
  shows "max_interval (assemble q b l)=approx_validity (assemble q b l)"
proof -
  have dom_eq: "approx_domain q={x. valid approximation_indices (d x) e}"
    by (simp add: approx_domain_def bridge)
  have ini: "initial (approx_domain q)"
    by (simp only: dom_eq, rule monotone_defects_initial[OF mono])
  show ?thesis by (rule interval_equals_initial_approx[OF ini])
qed

lemma assembled_signature_is_minimal:
  assumes rec: "\<And>x. recurs (f x) (e x) (c x) (q x)"
  shows "six_signature_output (assemble q b l)=set_signature (minimal_set (q l))"
  using Core_First_Failure_Report.minimal_signature_exact[
    where s="q l" and f="f l" and e="e l" and c="c l", OF rec]
  by (simp add: assemble_def)

definition normalized_family where
  "normalized_family q l t=(if t\<in>tokens then q l t else NotFormed)"

lemma native_solution_family_unique:
  assumes rec: "\<And>l. recurs (f l) (e l) (c l) (q l)"
  shows "normalized_family q=normalized_family (\<lambda>l. run (f l) (e l) (c l) 40)"
  using finite_run_unique[OF rec]
  by (auto simp: normalized_family_def fun_eq_iff)

lemma assembled_cong:
  assumes same: "\<And>l t. t\<in>tokens \<Longrightarrow> q l t=r l t"
  shows "assemble q b l=assemble r b l"
proof -
  have sd: "strict_domain q=strict_domain r"
    by (auto simp: strict_domain_def strict_complete_def series_complete_def same)
  have ad: "approx_domain q=approx_domain r"
    by (auto simp: approx_domain_def approx_complete_def series_complete_def same)
  have fd: "full_domain q=full_domain r" by (simp add: domain_intersection sd ad)
  have fs: "failed_set (q l)=failed_set (r l)"
    by (auto simp: failed_set_def same)
  have sig: "six_signature (q l)=six_signature (r l)"
    by (auto simp: six_signature_def fun_eq_iff same)
  show ?thesis by (simp add: assemble_def Core_First_Failure_Report.report_def
    multiplicity_report_def structural_case_def sd ad fd fs sig)
qed

lemma assembled_independent_of_solution:
  assumes hq: "\<And>x. recurs (f x) (e x) (c x) (q x)"
    and hr: "\<And>x. recurs (f x) (e x) (c x) (r x)"
  shows "assemble q b l=assemble r b l"
proof (rule assembled_cong)
  fix x t assume tt: "t\<in>tokens"
  show "q x t=r x t" using finite_run_unique[OF hq tt] finite_run_unique[OF hr tt] by simp
qed

definition generated where
  "generated f e c b l a = (\<exists>q. (\<forall>x. recurs (f x) (e x) (c x) (q x)) \<and> a=assemble q b l)"

lemma localization_data_unique: "\<exists>!a. generated f e c b l a"
proof -
  let ?q = "\<lambda>x. run (f x) (e x) (c x) 40"
  have rec: "\<And>x. recurs (f x) (e x) (c x) (?q x)" by (rule finite_run_solves)
  have exists: "generated f e c b l (assemble ?q b l)"
    unfolding generated_def by (rule exI[of _ ?q]) (simp add: rec)
  show ?thesis
  proof (rule ex1I[of _ "assemble ?q b l"])
    show "generated f e c b l (assemble ?q b l)" by (fact exists)
  next
    fix a assume "generated f e c b l a"
    then obtain r where hr: "\<And>x. recurs (f x) (e x) (c x) (r x)" and a: "a=assemble r b l"
      unfolding generated_def by blast
    have same: "assemble r b l=assemble ?q b l"
      by (rule assembled_independent_of_solution[OF hr rec])
    show "a=assemble ?q b l" using same a by simp
  qed
qed

ML \<open>
val roots = @{thms domain_intersection boundary_tokens_only_approx boundary_tokens_at_least
  no_boundary_no_tokens no_boundary_no_burden assembled_domain_intersection interval_within_approx
  interval_equals_initial_approx quantitative_interval assembled_signature_is_minimal
  native_solution_family_unique assembled_independent_of_solution localization_data_unique};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
