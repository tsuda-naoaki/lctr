theory Native_Law_Datum_Semantics
  imports "LCTR_Core_Native_Law_Failure.Core_Native_Law_Failure"
    "LCTR_Core_Law_Readiness.Core_Law_Readiness"
    "LCTR_Core_Stage_Boundaries.Core_Stage_Boundaries"
begin

definition native_law_operative where
  "native_law_operative dyn joint d \<longleftrightarrow>
    eval_spec d\<in>ready_set dyn joint \<and>
      Core_Native_Law_Family.all_conditions (family d)"

definition native_total_condition where
  "native_total_condition selection e i \<longleftrightarrow>
    (\<exists>d. selection e=Some d \<and> Core_Native_Law_Family.condition (family d) i)"

definition native_selected_failure where
  "native_selected_failure selection e \<longleftrightarrow>
    selection e\<noteq>None \<and> \<not>(\<forall>i. native_total_condition selection e i)"

definition local_native_family where
  "local_native_family d = (\<lambda>u::unit. family d)"

lemma selected_condition_exact:
  "selection e=Some d \<Longrightarrow>
    (native_total_condition selection e i \<longleftrightarrow>
      Core_Native_Law_Family.condition (family d) i)"
  by (simp add: native_total_condition_def)

lemma selected_all_conditions_exact:
  "selection e=Some d \<Longrightarrow>
    ((\<forall>i. native_total_condition selection e i) \<longleftrightarrow>
      Core_Native_Law_Family.all_conditions (family d))"
  by (simp add: native_total_condition_def Core_Native_Law_Family.all_conditions_exact)

context ready_selection
begin

lemma native_selected_datum_ready:
  "selection e=Some d \<Longrightarrow> eval_spec d\<in>ready_set dyn joint"
  by (rule selected_datum_ready)

end

locale ready_native_selection =
  ready_selection selection dyn
  for selection :: "'e \<Rightarrow> ('e,'j,('t,'a,'x,'y) law_family) law_datum option"
    and dyn :: "'e \<Rightarrow> bool"
begin

lemma native_law_operative_on_selected_datum:
  assumes sel: "selection e=Some d"
  shows "native_law_operative dyn joint d \<longleftrightarrow>
    Core_Native_Law_Family.all_conditions (family d)"
  by (simp add: native_law_operative_def selected_datum_ready[OF sel])

lemma native_failure_on_selected_datum:
  assumes sel: "selection e=Some d"
  shows "native_selected_failure selection e \<longleftrightarrow>
    \<not>Core_Native_Law_Family.all_conditions (family d)"
  by (simp add: native_selected_failure_def native_total_condition_def sel
    Core_Native_Law_Family.all_conditions_exact)

lemma native_failure_matches_family:
  assumes sel: "selection e=Some d"
  shows "native_selected_failure selection e \<longleftrightarrow>
    selected_law_family.failure {()} (local_native_family d) ()"
proof -
  have f: "selected_law_family.failure {()} (local_native_family d) ()
      \<longleftrightarrow> \<not>Core_Native_Law_Family.all_conditions (family d)"
    by (simp add: selected_law_family.failure_def selected_law_family.total_condition_def
      local_native_family_def Core_Native_Law_Family.all_conditions_exact)
  show ?thesis by (simp only: native_failure_on_selected_datum[OF sel] f)
qed

lemma native_failure_vs_operative:
  assumes sel: "selection e=Some d"
  shows "native_selected_failure selection e \<longleftrightarrow>
    dyn e \<and> \<not>native_law_operative dyn joint d"
  by (simp add: native_failure_on_selected_datum[OF sel]
    native_law_operative_on_selected_datum[OF sel] domain_ready[OF sel])

lemma native_law_failure_requires_dynamics:
  assumes h: "native_selected_failure selection e"
  shows "dyn e"
proof -
  obtain d where d: "selection e=Some d"
    using h unfolding native_selected_failure_def by (cases "selection e") auto
  show ?thesis by (rule domain_ready[OF d])
qed

end

lemma native_outside_selection:
  assumes "selection e=None"
  shows "(\<forall>i. \<not>native_total_condition selection e i) \<and>
    \<not>native_selected_failure selection e"
  by (simp add: assms native_total_condition_def native_selected_failure_def)

lemma native_dynamics_law_failures_disjoint:
  fixes selection :: "'e \<Rightarrow> ('e,'j,('t,'a,'x,'y) law_family) law_datum option"
    and K :: "'e \<Rightarrow> dynamics_index \<Rightarrow> bool"
  assumes ready: "ready_native_selection selection (\<lambda>e. exact_input e \<and> (\<forall>i. K e i))"
    and rec: "Core_Stage_Boundaries.recurs E formed evaluable cond st"
    and assign: "\<And>i. cond (token i) \<longleftrightarrow> K ev i"
  shows "\<not>((\<exists>i. st (token i)=Failed) \<and> native_selected_failure selection ev)"
proof
  interpret ready_native_selection selection "\<lambda>e. exact_input e \<and> (\<forall>i. K e i)"
    by (rule ready)
  assume both: "(\<exists>i. st (token i)=Failed) \<and> native_selected_failure selection ev"
  have all: "\<forall>i. K ev i"
    using native_law_failure_requires_dynamics[OF both[THEN conjunct2]] by blast
  obtain i where failed: "st (token i)=Failed" using both by blast
  have no: "\<not>cond (token i)" by (rule recursive_failed_condition[OF rec failed])
  have yes: "cond (token i)" using all[rule_format, of i] assign[of i] by simp
  show False using no yes by contradiction
qed

lemma fixed_carrier_operative_exact:
  "native_law_operative dyn joint d \<longleftrightarrow>
    Core_Law_Readiness.law_operative dyn joint Core_Native_Law_Family.condition d"
  by (simp add: native_law_operative_def Core_Law_Readiness.law_operative_def
    Core_Law_Readiness.all_conditions_def Core_Native_Law_Family.all_conditions_exact)

lemma native_candidate_condition_vector:
  "Core_Native_Law_Family.condition (family d) Law1 = K1 (family d) \<and>
   Core_Native_Law_Family.condition (family d) Law2 = K2 (family d) \<and>
   Core_Native_Law_Family.condition (family d) Law3 = K3 (family d) \<and>
   Core_Native_Law_Family.condition (family d) Law4 = K4 (family d) \<and>
   Core_Native_Law_Family.condition (family d) Law5 = K5 (family d)"
  by (rule condition_vector_exact)

ML \<open>
val roots = @{thms selected_condition_exact selected_all_conditions_exact
 ready_selection.native_selected_datum_ready ready_native_selection.native_law_operative_on_selected_datum
 ready_native_selection.native_failure_on_selected_datum ready_native_selection.native_failure_matches_family
 ready_native_selection.native_failure_vs_operative native_outside_selection
 ready_native_selection.native_law_failure_requires_dynamics native_dynamics_law_failures_disjoint
 fixed_carrier_operative_exact native_candidate_condition_vector};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
