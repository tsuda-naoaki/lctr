theory Core_Relative_State_Profile
  imports LCTR_Core_Localization_Bundle.Core_Localization_Bundle
begin

definition fiber where "fiber s v={t\<in>tokens. s t=v}"

lemma four_state_cover:
  "fiber s SAT\<union>fiber s Failed\<union>fiber s NotFormed\<union>fiber s NotEvaluable=tokens"
  by (rule set_eqI, rename_tac t, case_tac "s t") (auto simp: fiber_def)

lemma fibers_disjoint: "v\<noteq>w \<Longrightarrow> fiber s v\<inter>fiber s w={}"
  by (auto simp: fiber_def)

lemma unique_state_membership:
  assumes tt: "t\<in>tokens"
  shows "\<exists>!v. t\<in>fiber s v"
  by (rule ex1I[of _ "s t"]) (auto simp: fiber_def tt)

lemma full_iff_sat_universe: "full s = (fiber s SAT=tokens)"
  by (auto simp: series_completion_iff fiber_def)

lemma unique_series_membership:
  assumes tt: "t\<in>tokens"
  shows "\<exists>!i. i<6 \<and> fst t=i"
  using tt by (auto simp: tokens_def)

record 'a evaluation_profile =
  fully_valid :: bool
  state_fibers :: "internal_state\<Rightarrow>token set"
  profile_boundary :: "('a\<times>(nat\<Rightarrow>bool)) set"

definition profile where
  "profile q b l=\<lparr>fully_valid=full (q l),state_fibers=fiber (q l),
    profile_boundary=boundary_data (approx_domain q) (masked_signature b)\<rparr>"

lemma profile_and_localization_agree:
  "fully_valid (profile q b l)=(l\<in>full_validity (assemble q b l)) \<and>
    state_fibers (profile q b l) Failed=fst (first_failure (assemble q b l)) \<and>
    profile_boundary (profile q b l)=snd (snd (first_failure (assemble q b l)))"
  by (simp add: profile_def assemble_def full_domain_def
    Core_First_Failure_Report.report_def fiber_def failed_set_def)

lemma profile_cong:
  assumes same: "\<And>l t. t\<in>tokens \<Longrightarrow> q l t=r l t"
  shows "profile q b l=profile r b l"
proof -
  have full: "full (q l)=full (r l)" by (simp add: series_completion_iff same)
  have fibers: "fiber (q l)=fiber (r l)" by (auto simp: fiber_def fun_eq_iff same)
  have ad: "approx_domain q=approx_domain r"
    by (auto simp: approx_domain_def approx_complete_def series_complete_def same)
  show ?thesis by (simp add: profile_def full fibers ad)
qed

lemma combined_outputs_independent:
  assumes hq: "\<And>x. recurs (f x) (e x) (c x) (q x)"
    and hr: "\<And>x. recurs (f x) (e x) (c x) (r x)"
  shows "(profile q b l,assemble q b l)=(profile r b l,assemble r b l)"
proof -
  have same: "\<And>x t. t\<in>tokens \<Longrightarrow> q x t=r x t"
    using finite_run_unique[OF hq] finite_run_unique[OF hr] by metis
  have p: "profile q b l=profile r b l" by (rule profile_cong) (fact same)
  have a: "assemble q b l=assemble r b l" by (rule assembled_cong) (fact same)
  show ?thesis using p a by simp
qed

ML \<open>
val roots = @{thms four_state_cover fibers_disjoint unique_state_membership
  full_iff_sat_universe unique_series_membership profile_and_localization_agree
  combined_outputs_independent};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
