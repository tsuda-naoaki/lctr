theory Core_Audit_Report
  imports "../core_audit_groups/Core_Audit_Groups"
    "../core_audit_tags/Core_Audit_Tags"
    "../core_structural_burden/Core_Structural_Burden"
begin

type_synonym report_token = Core_Structural_Burden.native_token
type_synonym report_status = Core_Audit_State_Transport.audit_status
type_synonym report_reason = "report_token \<times> report_status"
typedef report_series = "{..<6::nat}"
  morphisms rep_series abs_series by (rule exI[of _ 0]) simp

lemma report_token_typed:
  "Core_Structural_Burden.rep_token t \<in> Core_Finite_Audit.tokens"
  using Core_Structural_Burden.rep_token[of t]
  by (auto simp: Core_Finite_Audit.tokens_def Core_Finite_Audit.count_def Core_Structural_Burden.count_def)
lemma report_token_inverse:
  "x\<in>Core_Finite_Audit.tokens \<Longrightarrow>
    Core_Structural_Burden.rep_token (Core_Structural_Burden.abs_token x)=x"
  by (rule Core_Structural_Burden.abs_token_inverse)
    (auto simp: Core_Finite_Audit.tokens_def Core_Finite_Audit.count_def Core_Structural_Burden.count_def)
lemma report_edge_exact:
  "Core_Structural_Burden.edge a b = Core_Finite_Audit.edge
    (Core_Structural_Burden.rep_token a) (Core_Structural_Burden.rep_token b)"
  by (simp add: Core_Structural_Burden.edge_def Core_Finite_Audit.edge_def
      Core_Structural_Burden.within_def Core_Finite_Audit.within_def)
lemma report_series_bound: "rep_series i<6"
  using rep_series[of i] by simp

definition pair_input where "pair_input f x = f (Core_Structural_Burden.abs_token x)"
definition report_audit where
  "report_audit s t = Core_Audit_Groups.native_status
    (Core_Finite_Audit.auditAt s (Core_Structural_Burden.rep_token t))"
definition report_output where
  "report_output f e q t = Core_Audit_Groups.native_status
    (Core_Finite_Audit.auditOutput (pair_input f) (pair_input e) (pair_input q)
      (Core_Structural_Burden.rep_token t))"
definition failed where "failed s = {t. s t=Core_Audit_State_Transport.Fail}"
definition failure_signature where "failure_signature s t = (s t=Core_Audit_State_Transport.Fail)"
definition approximation_group where
  "approximation_group = {t. fst (Core_Structural_Burden.rep_token t)=3}"
definition all_reasons where "all_reasons s = Core_Audit_Tags.reasons UNIV s"
definition local_reasons where "local_reasons s G = Core_Audit_Tags.group_reasons UNIV s G"

record state_report =
  group_states :: "report_series \<Rightarrow> report_status"
  condition_states :: "report_token \<Rightarrow> report_status"
  indeterminate_tokens :: "report_token set"
  indeterminate_signature :: "report_token \<Rightarrow> bool"
  undefined_reasons :: "report_reason set"
record 'b diagnostic_report =
  failed_position :: "report_token set + report_reason set"
  failure_signature_value :: "(report_token \<Rightarrow> bool) + report_reason set"
  approximation_boundary :: "'b + report_reason set"
  structural_burden :: "(Core_Structural_Burden.structural_token set \<times> Core_Structural_Burden.structural_token set) + report_reason set"
record ('d,'b) audit_report =
  report_data :: 'd
  report_states :: state_report
  report_diagnostics :: "'b diagnostic_report"

definition state_report where
  "state_report s = \<lparr>group_states = (\<lambda>i. Core_Audit_Groups.group_status (pair_input s) (rep_series i)),
    condition_states=s, indeterminate_tokens={t. s t=Core_Audit_State_Transport.Indeterminate},
    indeterminate_signature=(\<lambda>t. s t=Core_Audit_State_Transport.Indeterminate),
    undefined_reasons=all_reasons s\<rparr>"
definition diagnostics where
  "diagnostics s boundary boundary_roots = \<lparr>
    failed_position=Core_Audit_Tags.tagged (failed s) (all_reasons s),
    failure_signature_value=Core_Audit_Tags.tagged (failure_signature s) (all_reasons s),
    approximation_boundary=Core_Audit_Tags.tagged boundary (local_reasons s approximation_group),
    structural_burden=Core_Audit_Tags.tagged (Core_Structural_Burden.report (failed s) boundary_roots) (all_reasons s)\<rparr>"
definition assemble where
  "assemble data s boundary boundary_roots = \<lparr>report_data=data,
    report_states=state_report s, report_diagnostics=diagnostics s boundary boundary_roots\<rparr>"
definition native_report where
  "native_report data f e q boundary boundary_roots = assemble data (report_output f e q) boundary boundary_roots"
definition generated where
  "generated data f e q boundary boundary_roots r =
    (\<exists>s. Core_Finite_Audit.recurs (pair_input f) (pair_input e) (pair_input q) s \<and>
      r=assemble data (report_audit s) boundary boundary_roots)"

lemma union_group_reasons:
  "(\<Union>i<6. local_reasons s {t. fst (Core_Structural_Burden.rep_token t)=i})=all_reasons s"
proof -
  have bound: "\<And>t. fst (Core_Structural_Burden.rep_token t)<6"
  proof -
    fix t
    have h: "Core_Structural_Burden.rep_token t\<in>Core_Finite_Audit.tokens"
      by (rule report_token_typed)
    show "fst (Core_Structural_Burden.rep_token t)<6"
      using h by (cases "Core_Structural_Burden.rep_token t")
        (simp_all add: Core_Finite_Audit.tokens_def)
  qed
  show ?thesis using bound
    by (auto simp: local_reasons_def all_reasons_def Core_Audit_Tags.group_reasons_def)
qed
lemma approximation_reasons_subset:
  "local_reasons s approximation_group \<subseteq> all_reasons s"
  by (auto simp: local_reasons_def all_reasons_def Core_Audit_Tags.group_reasons_def)
lemma report_preserves_data:
  "report_data (native_report data f e q boundary boundary_roots)=data"
  by (simp add: native_report_def assemble_def)
lemma native_report_matches:
  assumes rec: "Core_Finite_Audit.recurs (pair_input f) (pair_input e) (pair_input q) s"
  shows "assemble data (report_audit s) boundary boundary_roots =
    native_report data f e q boundary boundary_roots"
proof -
  have eq: "report_audit s=report_output f e q"
    by (rule ext) (simp add: report_audit_def report_output_def
      Core_Finite_Audit.finite_audit_output_unique[OF rec report_token_typed])
  show ?thesis by (simp only: eq native_report_def)
qed
lemma report_independent_of_solution:
  "Core_Finite_Audit.recurs (pair_input f) (pair_input e) (pair_input q) s \<Longrightarrow>
   Core_Finite_Audit.recurs (pair_input f) (pair_input e) (pair_input q) t \<Longrightarrow>
   assemble data (report_audit s) boundary boundary_roots =
   assemble data (report_audit t) boundary boundary_roots"
  by (metis native_report_matches)
lemma native_report_unique:
  "\<exists>!r. generated data f e q boundary boundary_roots r"
proof (rule ex1I[of _ "native_report data f e q boundary boundary_roots"])
  show "generated data f e q boundary boundary_roots
    (native_report data f e q boundary boundary_roots)"
    unfolding generated_def
    using Core_Finite_Audit.finite_run_solves native_report_matches by metis
next
  fix r assume "generated data f e q boundary boundary_roots r"
  then obtain s where rec: "Core_Finite_Audit.recurs (pair_input f) (pair_input e) (pair_input q) s"
    and r: "r=assemble data (report_audit s) boundary boundary_roots"
    unfolding generated_def by blast
  show "r=native_report data f e q boundary boundary_roots"
    by (simp only: r native_report_matches[OF rec])
qed
lemma native_group_maximum:
  assumes t: "fst (Core_Structural_Burden.rep_token t)=rep_series i"
  shows "Core_Audit_State_Transport.priority (condition_states (report_states
      (native_report data f e q boundary boundary_roots)) t) \<le>
    Core_Audit_State_Transport.priority (group_states (report_states
      (native_report data f e q boundary boundary_roots)) i)"
proof -
  have mem: "Core_Structural_Burden.rep_token t\<in>Core_Audit_Groups.group_tokens (rep_series i)"
    using report_token_typed[of t] t by (simp add: Core_Audit_Groups.group_tokens_def)
  note h=Core_Audit_Groups.group_maximum[OF report_series_bound mem, where s="pair_input (report_output f e q)"]
  show ?thesis using h by (simp add: native_report_def assemble_def state_report_def pair_input_def
    Core_Structural_Burden.rep_token_inverse)
qed
lemma native_failure_signature:
  "failure_signature (report_output f e q) t \<longleftrightarrow>
    Core_Finite_Audit.run (pair_input f) (pair_input e) (pair_input q) 40
      (Core_Structural_Burden.rep_token t)=Core_Finite_Audit.Failed"
proof -
  have eq: "(Core_Structural_Burden.rep_token t\<in>{x\<in>Core_Finite_Audit.tokens.
      Core_Audit_Groups.native_status (Core_Finite_Audit.auditOutput (pair_input f) (pair_input e) (pair_input q) x)=Core_Audit_State_Transport.Fail})
    = (Core_Structural_Burden.rep_token t\<in>{x\<in>Core_Finite_Audit.tokens.
      Core_Finite_Audit.run (pair_input f) (pair_input e) (pair_input q) 40 x=Core_Finite_Audit.Failed})"
    by (simp only: Core_Audit_Groups.native_failed_fiber)
  show ?thesis using eq report_token_typed[of t]
    by (simp add: failure_signature_def report_output_def)
qed
lemma native_indeterminate_signature:
  "indeterminate_signature (report_states (native_report data f e q boundary boundary_roots)) t
    \<longleftrightarrow> t\<in>indeterminate_tokens (report_states (native_report data f e q boundary boundary_roots))"
  by (simp add: native_report_def assemble_def state_report_def)
lemma approximation_boundary_uses_local_reasons:
  "local_reasons s approximation_group={} \<Longrightarrow>
    approximation_boundary (diagnostics s boundary boundary_roots)=Inl boundary"
  by (simp add: diagnostics_def Core_Audit_Tags.tagged_def)
lemma failed_position_uses_global_reasons:
  "all_reasons s\<noteq>{} \<Longrightarrow>
    failed_position (diagnostics s boundary boundary_roots)=Inr (all_reasons s)"
  by (simp add: diagnostics_def Core_Audit_Tags.tagged_def)
lemma diagnostic_values_when_defined:
  assumes h: "all_reasons s={}"
  shows "diagnostics s boundary boundary_roots = \<lparr>
    failed_position=Inl (failed s), failure_signature_value=Inl (failure_signature s),
    approximation_boundary=Inl boundary,
    structural_burden=Inl (Core_Structural_Burden.report (failed s) boundary_roots)\<rparr>"
proof -
  have local: "local_reasons s approximation_group={}"
    using approximation_reasons_subset[of s] h by blast
  show ?thesis by (simp add: diagnostics_def h local Core_Audit_Tags.tagged_def)
qed

ML \<open>
val roots = @{thms union_group_reasons approximation_reasons_subset report_preserves_data native_report_matches report_independent_of_solution native_report_unique native_group_maximum native_failure_signature native_indeterminate_signature approximation_boundary_uses_local_reasons failed_position_uses_global_reasons diagnostic_values_when_defined};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
