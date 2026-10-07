theory Native_Family_Alignment
  imports "LCTR_Native_Family_Fibre_Conditions.Native_Family_Fibre_Conditions"
begin
context native_family_component_atlas
begin
definition value_chart_data :: "('c set set \<Rightarrow> real) \<Rightarrow> _" where
  "value_chart_data rho = (ID, IT, ic, OD, OT, oc)"
lemma shared_value_charts: "value_chart_data rho = value_chart_data other"
  by (simp only: value_chart_data_def)
end

lemma full_family_failure_cover:
  "\<not>family_complete Reps Selected p \<longleftrightarrow>
    \<not>family_first Reps Selected p \<or>
    (family_first Reps Selected p \<and> \<not>family_second Reps Selected p) \<or>
    (family_first Reps Selected p \<and> family_second Reps Selected p \<and> \<not>family_third Reps Selected p) \<or>
    (family_first Reps Selected p \<and> \<not>family_fourth Reps Selected p) \<or>
    (family_first Reps Selected p \<and> \<not>family_fifth Reps Selected p)"
  by (auto simp only: family_complete_def)

lemmas same_transported_input_value = generated_law_representations.same_transported_input_value
lemmas same_transported_output_value = generated_law_representations.same_transported_output_value
lemmas between_preserves_native_values = generated_law_representations.between_preserves_native_values
lemmas native_first_condition = native_family_component_atlas.first_condition_exact
  native_family_component_atlas.first_projection_exact family_first_def
lemmas native_second_condition = native_family_component_atlas.second_condition_exact
  native_family_component_atlas.second_projection_exact family_second_def
lemmas native_third_condition = native_family_component_atlas.third_condition_all_representations
  native_family_component_atlas.third_projection_exact family_third_def
lemmas native_fourth_condition = native_family_component_atlas.fourth_condition_exact
  native_family_component_atlas.fourth_projection_exact family_fourth_def
lemmas native_fifth_condition = native_family_component_atlas.fifth_condition_exact
  native_family_component_atlas.fifth_projection_exact family_fifth_def
lemmas same_law_data_all_representations = native_family_component_atlas.same_generated_law_values
lemmas shared_value_charts = native_family_component_atlas.shared_value_charts
lemmas native_failure_cover = full_family_failure_cover
  native_family_component_atlas.native_five_failure_cover family_assembly_exact

ML \<open>
val roots = @{thms same_transported_input_value same_transported_output_value
  between_preserves_native_values native_first_condition native_second_condition
  native_third_condition native_fourth_condition native_fifth_condition
  same_law_data_all_representations shared_value_charts native_failure_cover};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
