theory Chapter02_Role_Alignment
  imports "LCTR_Core_Carrier_Patterns.Core_Carrier_Patterns"
begin

definition typed_role_family where "typed_role_family a = ri_family id (component_at a) (selected_indices a)"
definition typed_role_bundle where "typed_role_bundle a z = role_bundle id (component_at a) z"
definition family_positions where
  "family_positions a z \<longleftrightarrow>
    ri_zeta (bundle_clock (typed_role_bundle a z))=z \<and>
    ri_zeta (bundle_detector (typed_role_bundle a z))=z \<and>
    ri_zeta (bundle_body (typed_role_bundle a z))=z \<and>
    ri_zeta (bundle_observer (typed_role_bundle a z))=z \<and>
    ri_role (bundle_clock (typed_role_bundle a z))=Clock \<and>
    ri_role (bundle_detector (typed_role_bundle a z))=Detector \<and>
    ri_role (bundle_body (typed_role_bundle a z))=Body \<and>
    ri_role (bundle_observer (typed_role_bundle a z))=Observer"

record ('z,'l,'p) role_realization =
  realization_carrier :: "'p set"
  realization_map :: "'z\<Rightarrow>realization_role\<Rightarrow>('z,'l) role_instance\<Rightarrow>'p"
definition typed_role_realization where
  "typed_role_realization a p \<longleftrightarrow> (\<forall>z\<in>selected_indices a. \<forall>r.
    realization_map p z r (role_at a (role_of_realization r) z)\<in>realization_carrier p)"
definition typed_attach_realization where "typed_attach_realization a p = (typed_role_family a,p)"

lemma alignment_roleInstance_eq_iff_index_eq:
  "role_at a r z=role_at a r w \<longleftrightarrow> z=w"
  by (simp add: role_at_def role_instance_eq_iff_index_eq)
lemma alignment_riFamily_preserves_index_and_role_positions:
  "z\<in>selected_indices a \<Longrightarrow> (z,typed_role_bundle a z)\<in>typed_role_family a \<and> family_positions a z"
  by (simp add: typed_role_family_def typed_role_bundle_def family_positions_def ri_family_def role_bundle_def role_instance_def)
lemma alignment_body_abstraction_source_preserved:
  "valid_carrier_input a \<Longrightarrow> z\<in>selected_indices a \<Longrightarrow>
    abstracted_from a (tracked_at a z) (scene_at a z) (component_at a z Body)"
  by (auto simp: valid_carrier_input_def)
lemma alignment_realizationRole_cases:
  "role_of_realization r=Clock \<or> role_of_realization r=Detector \<or> role_of_realization r=Observer"
  by (rule realization_role_cases)
lemma alignment_realization_input_excludes_body:
  "ri_role (role_at a (role_of_realization r) z)\<noteq>Body"
  using realization_role_not_body by (simp add: role_at_def role_instance_def)
lemma alignment_realization_is_additional_and_preserves_existing_ri:
  "fst (typed_attach_realization a p)=typed_role_family a"
  by (simp add: typed_attach_realization_def)
lemma alignment_section2_synthesis_preserves_positions:
  "z\<in>selected_indices a \<Longrightarrow> (z,typed_role_bundle a z)\<in>typed_role_family a \<and> family_positions a z"
  by (rule alignment_riFamily_preserves_index_and_role_positions)
lemma alignment_section2_synthesis_body_source:
  "valid_carrier_input a \<Longrightarrow> z\<in>selected_indices a \<Longrightarrow>
    abstracted_from a (tracked_at a z) (scene_at a z) (component_at a z Body)"
  by (rule alignment_body_abstraction_source_preserved)
lemma alignment_section2_synthesis_realization_domain:
  "ri_role (role_at a (role_of_realization r) z)=role_of_realization r \<and> role_of_realization r\<noteq>Body"
  using realization_role_not_body by (simp add: role_at_def role_instance_def)
lemma alignment_different_indices_remain_distinct_at_each_role:
  "z\<noteq>w \<Longrightarrow> role_at a r z\<noteq>role_at a r w"
  by (simp add: alignment_roleInstance_eq_iff_index_eq)
lemma alignment_different_role_positions_remain_distinct:
  "role_at a Clock z\<noteq>role_at a Body z"
  by (simp add: role_at_def role_instance_def)

definition specified_data where
  "specified_data a z = (tracked_at a z,scene_at a z,component_at a z)"
definition tiny_typed_input :: "(bool,unit,unit,unit) carrier_input" where
  "tiny_typed_input = \<lparr>selected_indices=UNIV,local_carrier=(\<lambda>_ _. UNIV),
    scene_at=(\<lambda>_. ()),tracked_at=(\<lambda>_. ()),component_at=(\<lambda>_ _. ()),
    correspondence_entered=(\<lambda>_ _ _ _. True),detector_retains=(\<lambda>_ _ _ _. True),
    observer_receives=(\<lambda>_ _ _ _ _. True),observer_combines=(\<lambda>_ _ _ _ _. True),
    abstracted_from=(\<lambda>_ _ _. True)\<rparr>"
lemma tiny_typed_input_valid: "valid_carrier_input tiny_typed_input"
  by (simp add: tiny_typed_input_def valid_carrier_input_def)
lemma alignment_distinct_zeta_same_object_scene_and_bind_witness:
  "specified_data tiny_typed_input True=specified_data tiny_typed_input False"
  by (simp add: specified_data_def tiny_typed_input_def)
lemma alignment_distinct_zeta_same_specified_data_still_distinct_in_every_role:
  "\<forall>r. role_at tiny_typed_input r True\<noteq>role_at tiny_typed_input r False"
  by (simp add: alignment_roleInstance_eq_iff_index_eq)

lemma actual_binding_and_scene_preserved:
  assumes a: "valid_carrier_input a" and z: "z\<in>selected_indices a"
  shows "(\<forall>r. ri_component (role_at a r z)\<in>local_carrier a (scene_at a z) r) \<and>
    correspondence_entered a (scene_at a z) (component_at a z Clock) (component_at a z Body) (component_at a z Detector) \<and>
    detector_retains a (scene_at a z) (component_at a z Clock) (component_at a z Body) (component_at a z Detector) \<and>
    observer_receives a (scene_at a z) (component_at a z Clock) (component_at a z Detector) (component_at a z Body) (component_at a z Observer) \<and>
    observer_combines a (scene_at a z) (component_at a z Clock) (component_at a z Detector) (component_at a z Body) (component_at a z Observer)"
  using a z by (auto simp: valid_carrier_input_def role_at_def role_instance_def)
lemma typed_family_function_exact:
  "(z,b)\<in>typed_role_family a \<longleftrightarrow> z\<in>selected_indices a \<and> b=typed_role_bundle a z"
  by (auto simp: typed_role_family_def typed_role_bundle_def ri_family_def)
lemma typed_family_empty:
  "selected_indices a={} \<Longrightarrow> typed_role_family a={}"
  by (simp add: typed_role_family_def ri_family_def)
lemma typed_realization_singleton_domain:
  assumes p: "typed_role_realization a p" and z: "z\<in>selected_indices a"
    and x: "x=role_at a (role_of_realization r) z"
  shows "realization_map p z r x\<in>realization_carrier p"
  using p z x unfolding typed_role_realization_def by blast
lemma typed_attach_preserves_realization:
  "snd (typed_attach_realization a p)=p"
  by (simp add: typed_attach_realization_def)

ML \<open>
val roots = @{thms alignment_roleInstance_eq_iff_index_eq alignment_riFamily_preserves_index_and_role_positions
  alignment_body_abstraction_source_preserved alignment_realizationRole_cases alignment_realization_input_excludes_body
  alignment_realization_is_additional_and_preserves_existing_ri alignment_section2_synthesis_preserves_positions
  alignment_section2_synthesis_body_source alignment_section2_synthesis_realization_domain
  alignment_different_indices_remain_distinct_at_each_role alignment_different_role_positions_remain_distinct
  alignment_distinct_zeta_same_object_scene_and_bind_witness alignment_distinct_zeta_same_specified_data_still_distinct_in_every_role};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
