theory Native_Differential_Synthesis_Alignment
  imports "LCTR_Native_Differential_Law_Binding.Native_Differential_Law_Binding"
    "LCTR_Native_Family_Value_Images.Native_Family_Value_Images"
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

lemma same_input_native_synthesis:
  assumes lawop: "all_conditions (candidates Jlaw comp allowed faithful)" and h: "diff.Complete Rel"
  shows "(\<forall>other\<in>diff.Reps. \<exists>!x. transported_spec other Jlaw comp allowed faithful x \<and>
      all_conditions (snd x) \<and> (\<forall>jj. Core_Native_Law_Family.components (snd x) jj = diff.component_at other jj)) \<and>
    (\<forall>other\<in>diff.Reps. diff.RegularAt other (diff.ChosenRegular other)) \<and>
    (\<forall>other\<in>diff.Reps. \<forall>alpha beta gamma. \<forall>theta\<in>diff.Numeric other alpha beta gamma.
      diff.Pair other alpha beta gamma theta\<in>Rel other alpha (beta,gamma)) \<and>
    (\<forall>other\<in>diff.Reps. diff.CovAt other (diff.ChosenRegular other) (Rel other)) \<and>
    (\<forall>other\<in>diff.Reps. \<forall>nextrep\<in>diff.Reps. diff.TimeAt other nextrep (Rel other) (Rel nextrep))"
proof -
  have cores: "\<forall>other\<in>diff.Reps. \<exists>!x. transported_spec other Jlaw comp allowed faithful x \<and>
    all_conditions (snd x) \<and> (\<forall>jj. Core_Native_Law_Family.components (snd x) jj = diff.component_at other jj)"
    by (intro ballI; rule same_law_core_and_components[OF diff.family_typed lawop]; assumption)
  show ?thesis using cores diff.native_component_synthesis[OF h] by blast
qed
end
end

lemma all_component_consequences:
  assumes core: "\<forall>r\<in>Reps. Core r"
    and component: "\<forall>j\<in>Selected.
      (\<forall>r\<in>Reps. Reg r j) \<and> (\<forall>r\<in>Reps. Member r j) \<and>
      (\<forall>r\<in>Reps. Cov r j) \<and> (\<forall>r\<in>Reps. \<forall>s\<in>Reps. Time r s j)"
  shows "(\<forall>r\<in>Reps. Core r) \<and>
    (\<forall>r\<in>Reps. \<forall>j\<in>Selected. Reg r j) \<and>
    (\<forall>r\<in>Reps. \<forall>j\<in>Selected. Member r j) \<and>
    (\<forall>r\<in>Reps. \<forall>j\<in>Selected. Cov r j) \<and>
    (\<forall>r\<in>Reps. \<forall>s\<in>Reps. \<forall>j\<in>Selected. Time r s j)"
  using core component by blast

lemmas same_law_objects_every_representation = native_dynamics_bundle.same_law_core_and_components
lemmas native_generated_jet_membership = native_family_component_atlas.native_generated_jet_membership
lemmas native_flat_jet_membership = native_family_component_atlas.native_flat_jet_membership
lemmas native_zeroth_values = native_family_component_atlas.native_zeroth_values
lemmas native_value_relation_image = native_family_component_atlas.native_value_relation_image_via_model
  native_family_component_atlas.native_value_relation_image_zero positive_pair_model zero_left_model zero_right_model
lemmas native_time_relation_image = native_family_component_atlas.native_time_relation_image
lemmas time_change_zeroth_value = native_family_component_atlas.time_change_zeroth_value
lemmas time_order_isomorphism_unique = generated_law_representations.full_time_image_order_isomorphism
lemmas native_differential_synthesis = native_dynamics_bundle.same_input_native_synthesis all_component_consequences

ML \<open>
val roots = @{thms same_law_objects_every_representation native_generated_jet_membership
  native_flat_jet_membership native_zeroth_values native_value_relation_image
  native_time_relation_image time_change_zeroth_value time_order_isomorphism_unique
  native_differential_synthesis};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
