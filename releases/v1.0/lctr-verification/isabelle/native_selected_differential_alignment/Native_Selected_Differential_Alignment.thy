theory Native_Selected_Differential_Alignment
  imports "LCTR_Native_Selected_Family_Guards.Native_Selected_Family_Guards"
begin

context native_dynamics_bundle
begin
context
  fixes Jlaw comp allowed faithful j k TD TT tc ID IT ic OD OT oc
  assumes atlas: "native_family_component_atlas C D B R Bind source_order rho
    (candidates Jlaw comp allowed faithful) j k TD TT tc ID IT ic OD OT oc"
begin
interpretation diff: native_family_component_atlas C D B R Bind source_order rho
  "candidates Jlaw comp allowed faithful" j k TD TT tc ID IT ic OD OT oc
  by (rule atlas)

lemma selected_actual_native_synthesis:
  assumes selection: "native_family_selection lawDomain diffDomain"
    and dom: "ev\<in>diffDomain"
    and law_owned: "lawDatum ev = candidates Jlaw comp allowed faithful"
    and differential_owned: "data ev = diff.failure_input Rel"
    and op: "native_family_selection.selectedOperative diffDomain lawDatum data all_conditions ev"
  shows "(\<forall>other\<in>diff.Reps. \<exists>!x. transported_spec other Jlaw comp allowed faithful x \<and>
      all_conditions (snd x) \<and> (\<forall>jj. Core_Native_Law_Family.components (snd x) jj = diff.component_at other jj)) \<and>
    (\<forall>other\<in>diff.Reps. \<forall>alpha beta gamma. \<forall>theta\<in>diff.Numeric other alpha beta gamma.
      diff.Pair other alpha beta gamma theta\<in>Rel other alpha (beta,gamma)) \<and>
    (\<forall>other\<in>diff.Reps. diff.CovAt other (diff.ChosenRegular other) (Rel other)) \<and>
    (\<forall>other\<in>diff.Reps. \<forall>nextrep\<in>diff.Reps. diff.TimeAt other nextrep (Rel other) (Rel nextrep))"
proof -
  interpret sel: native_family_selection lawDomain diffDomain lawDatum data all_conditions
    by (rule selection)
  have unpack: "all_conditions (candidates Jlaw comp allowed faithful) \<and>
      (\<forall>i. Core_Differential_Failure.condition (diff.failure_input Rel) i)"
    using sel.operative_on_domain[OF dom] op law_owned differential_owned by simp
  have complete: "diff.Complete Rel"
    using unpack diff.actual_failure_input_complete by blast
  show ?thesis using same_input_native_synthesis[OF atlas unpack[THEN conjunct1] complete] by blast
qed
end
end

lemmas selected_law_owned = native_family_selection.selected_law_owned
lemmas selected_differential_owned = native_family_selection.selected_differential_owned
lemmas operative_on_domain = native_family_selection.operative_on_domain
lemmas operative_requires_same_law = native_family_selection.operative_requires_same_law
lemmas outside_selection_unformed = native_family_selection.outside_selection_unformed
lemmas selected_condition_native = native_family_selection.selected_condition_native
lemmas selected_failure_exact = native_family_selection.selected_failure_exact
lemmas selected_minimal_counter = native_family_selection.selected_minimal_counter
lemmas selected_failure_cover = native_family_selection.selected_failure_cover
lemmas selected_native_synthesis = native_dynamics_bundle.selected_actual_native_synthesis all_component_consequences

ML \<open>
val roots = @{thms selected_law_owned selected_differential_owned operative_on_domain
  operative_requires_same_law outside_selection_unformed selected_condition_native
  selected_failure_exact selected_minimal_counter selected_failure_cover selected_native_synthesis};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
