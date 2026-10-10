theory Core_Law_Readiness
  imports LCTR_Core_Law_Failure.Core_Law_Failure
begin

record ('e,'j,'f) law_datum =
  eval_spec :: "'e + 'j"
  family :: "'f"

definition ready_set where
  "ready_set dyn joint = Inl ` {e. dyn e} \<union> Inr ` {j. joint j}"
definition all_conditions where
  "all_conditions condition f \<longleftrightarrow> (\<forall>i::law_node. condition f i)"
definition law_operative where
  "law_operative dyn joint condition d \<longleftrightarrow>
    eval_spec d\<in>ready_set dyn joint \<and> all_conditions condition (family d)"
definition selected_condition where
  "selected_condition selection condition e i \<longleftrightarrow>
    (\<exists>d. selection e=Some d \<and> condition (family d) i)"
definition selected_failure where
  "selected_failure selection condition e \<longleftrightarrow>
    selection e\<noteq>None \<and> \<not>(\<forall>i::law_node. selected_condition selection condition e i)"

lemma single_ready_exact: "Inl e\<in>ready_set dyn joint \<longleftrightarrow> dyn e"
  unfolding ready_set_def by auto

locale ready_selection =
  fixes selection :: "'e\<Rightarrow>('e,'j,'f) law_datum option"
    and dyn :: "'e\<Rightarrow>bool"
  assumes domain_ready: "\<And>e d. selection e=Some d \<Longrightarrow> dyn e"
    and same_spec: "\<And>e d. selection e=Some d \<Longrightarrow> eval_spec d=Inl e"
begin

lemma selected_datum_ready:
  assumes sel: "selection e=Some d"
  shows "eval_spec d\<in>ready_set dyn joint"
  using same_spec[OF sel] domain_ready[OF sel] by (simp add: single_ready_exact)

lemma law_operative_on_selected_datum:
  assumes sel: "selection e=Some d"
  shows "law_operative dyn joint condition d \<longleftrightarrow> all_conditions condition (family d)"
  unfolding law_operative_def using selected_datum_ready[OF sel] by simp

lemma law_failure_requires_dynamics:
  assumes fail: "selected_failure selection condition e"
  shows "dyn e"
proof -
  obtain d where sel: "selection e=Some d"
    using fail unfolding selected_failure_def by (cases "selection e") auto
  show ?thesis by (rule domain_ready[OF sel])
qed

lemma failure_vs_operative:
  assumes sel: "selection e=Some d"
  shows "selected_failure selection condition e \<longleftrightarrow>
    dyn e \<and> \<not>law_operative dyn joint condition d"
  using domain_ready[OF sel] law_operative_on_selected_datum[OF sel]
  unfolding selected_failure_def selected_condition_def all_conditions_def
  by (simp add: sel)

lemma no_failure_outside_selected_domain:
  "selection e=None \<Longrightarrow> \<not>selected_failure selection condition e"
  unfolding selected_failure_def by simp
end

lemma proper_subdomain_permitted:
  "\<exists>(selected::bool\<Rightarrow>bool) dyn.
    (\<forall>e. selected e \<longrightarrow> dyn e) \<and> \<not>(\<forall>e. selected e \<longleftrightarrow> dyn e)"
  by (intro exI[where x="\<lambda>e::bool. e=False"] exI[where x="\<lambda>_::bool. True"]) auto

ML \<open>
val roots = @{thms single_ready_exact ready_selection.selected_datum_ready
  ready_selection.law_operative_on_selected_datum ready_selection.law_failure_requires_dynamics
  ready_selection.failure_vs_operative ready_selection.no_failure_outside_selected_domain
  proper_subdomain_permitted};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
