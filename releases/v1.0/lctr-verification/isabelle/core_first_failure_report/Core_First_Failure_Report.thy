theory Core_First_Failure_Report
  imports LCTR_Core_Comparison_Scope.Core_Comparison_Scope
    LCTR_Core_First_Boundary.Core_First_Boundary
    LCTR_Core_Continuum_Boundary.Core_Continuum_Boundary
begin

definition six_signature where
  "six_signature s t = (t\<in>tokens \<and> s t=Failed)"
definition set_signature where
  "set_signature S t = (t\<in>tokens \<and> t\<in>S)"

lemma minimal_positions_exact:
  "recurs f e c s \<Longrightarrow> minimal_set s=failed_set s"
  by (rule recursive_native.minimal_positions_exact) (unfold_locales, assumption)

lemma signature_support_exact:
  "six_signature s t = (t\<in>failed_set s)"
  by (simp add: six_signature_def failed_set_def)

lemma minimal_signature_exact:
  assumes rec: "recurs f e c s"
  shows "six_signature s=set_signature (minimal_set s)"
  using minimal_positions_exact[OF rec]
  by (auto simp: six_signature_def set_signature_def failed_set_def fun_eq_iff)

lemma localization_nonempty:
  "recurs f e c s \<Longrightarrow> failed_set s\<noteq>{} \<Longrightarrow> minimal_set s\<noteq>{}"
  using minimal_positions_exact by blast

datatype structural_class = NoFailure | SingleFailure | ParallelFailure
definition structural_case where
  "structural_case s = (if card (failed_set s)=0 then NoFailure
    else if card (failed_set s)=1 then SingleFailure else ParallelFailure)"

lemma finite_failed_set: "finite (failed_set s)"
proof -
  have finite_tokens: "finite tokens" using finite_set[of token_list] token_list_exact by simp
  show ?thesis using finite_tokens by (simp add: failed_set_def)
qed

lemma unique_structural_position:
  assumes "structural_case s=SingleFailure"
  shows "\<exists>t\<in>tokens. failed_set s={t} \<and> (\<forall>u\<in>tokens. six_signature s u = (u=t))"
proof -
  have card: "card (failed_set s)=1"
    using assms by (auto simp: structural_case_def split: if_splits)
  obtain t where single: "failed_set s={t}" using card by (rule card_1_singletonE)
  have typed: "t\<in>tokens" using single unfolding failed_set_def by blast
  show ?thesis
    using single typed by (auto simp: signature_support_exact)
qed

lemma parallel_structural_positions:
  "structural_case s=ParallelFailure \<Longrightarrow> 2\<le>card (failed_set s)"
  by (auto simp: structural_case_def split: if_splits)

lemmas boundary_singleton = Core_First_Boundary.boundary_singleton
lemmas boundary_empty_iff = Core_First_Boundary.boundary_empty_iff
lemmas boundary_empty_or_singleton = Core_First_Boundary.boundary_empty_or_singleton
lemmas full_validity_has_no_boundary = Core_First_Boundary.full_validity_has_no_boundary
lemmas no_least_boundary_control = Core_First_Boundary.no_least_boundary_control
lemmas boundary_presence_different_from_zero_signature =
  Core_First_Boundary.boundary_presence_different_from_zero_signature

definition approximation_indices :: "nat set" where "approximation_indices={1..9}"
definition excess_signature where
  "excess_signature d e i = (i\<in>exceeded approximation_indices d e)"

lemma excess_signature_exact:
  assumes di: "0\<le>d i" and ei: "0\<le>e i" and ii: "i\<in>approximation_indices"
  shows "excess_signature d e i = (e i<d i)"
  using excess_positive[OF ei di]
  by (simp add: excess_signature_def exceeded_def ii)

lemma excess_signature_zero_iff:
  assumes d: "\<And>i. i\<in>approximation_indices \<Longrightarrow> 0\<le>d i"
    and e: "\<And>i. i\<in>approximation_indices \<Longrightarrow> 0\<le>e i"
  shows "(excess_signature d e=(\<lambda>_. False)) = valid approximation_indices d e"
proof -
  interpret N: nonnegative_family approximation_indices d e by standard (fact d, fact e)
  show ?thesis using N.validity_characterizations
    by (auto simp: excess_signature_def fun_eq_iff)
qed

lemma quantitative_boundary_singleton:
  fixes d :: "'a::linorder\<Rightarrow>nat\<Rightarrow>ereal" and e :: "nat\<Rightarrow>ereal"
  assumes d: "\<And>x i. i\<in>approximation_indices \<Longrightarrow> 0\<le>d x i"
    and e: "\<And>i. i\<in>approximation_indices \<Longrightarrow> 0\<le>e i"
    and least: "least_outside {x. valid approximation_indices (d x) e} l"
  shows "boundary_data {x. valid approximation_indices (d x) e}
      (\<lambda>x. excess_signature (d x) e) = {(l,excess_signature (d l) e)} \<and>
      excess_signature (d l) e\<noteq>(\<lambda>_. False)"
proof -
  have single: "boundary_data {x. valid approximation_indices (d x) e}
      (\<lambda>x. excess_signature (d x) e) = {(l,excess_signature (d l) e)}"
    by (rule boundary_singleton[OF least])
  have invalid: "\<not>valid approximation_indices (d l) e"
    using least by (simp add: least_outside_def)
  have nonzero: "excess_signature (d l) e\<noteq>(\<lambda>_. False)"
    using excess_signature_zero_iff[where d="d l" and e=e, OF d e] invalid by blast
  show ?thesis using single nonzero by simp
qed

definition report where
  "report s V b = (failed_set s, six_signature s, boundary_data V b)"

lemma report_independent_of_solution:
  assumes hs: "recurs f e c s" and ht: "recurs f e c t"
  shows "report s V b=report t V b"
proof -
  have point: "\<And>u. u\<in>tokens \<Longrightarrow> s u=t u"
    using finite_run_unique[OF hs] finite_run_unique[OF ht] by metis
  have fs: "failed_set s=failed_set t" by (auto simp: failed_set_def point)
  have sig: "six_signature s=six_signature t"
    by (auto simp: six_signature_def fun_eq_iff point)
  show ?thesis by (simp add: report_def fs sig)
qed

lemma report_components:
  assumes rec: "recurs f e c s"
  shows "fst (report s V b)=minimal_set s \<and>
    fst (snd (report s V b))=set_signature (failed_set s) \<and>
    (snd (snd (report s V b))={} \<or>
      (\<exists>l. snd (snd (report s V b))={(l,b l)}))"
  using minimal_positions_exact[OF rec] boundary_empty_or_singleton[of V b]
  by (auto simp: report_def six_signature_def set_signature_def failed_set_def fun_eq_iff)

ML \<open>
val roots = @{thms minimal_positions_exact signature_support_exact minimal_signature_exact
  localization_nonempty unique_structural_position parallel_structural_positions
  boundary_singleton boundary_empty_iff boundary_empty_or_singleton full_validity_has_no_boundary
  excess_signature_exact excess_signature_zero_iff quantitative_boundary_singleton
  report_independent_of_solution report_components no_least_boundary_control
  boundary_presence_different_from_zero_signature};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
