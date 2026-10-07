theory Native_Metadata_01_025
imports
  "LCTR_Core_Continuum_Input.Core_Continuum_Input"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Input.affine_frequency.count_evaluation_source_exact",
  "Core_Continuum_Input.affine_frequency.step_width_positive",
  "Core_Continuum_Input.closure_contains_inputs",
  "Core_Continuum_Input.closure_is_closed",
  "Core_Continuum_Input.closure_is_least",
  "Core_Continuum_Input.continuum_input.generated_coordinate_candidates_exact",
  "Core_Continuum_Input.continuum_input.generated_input_retains_inputs",
  "Core_Continuum_Input.continuum_input.generated_record_truths_exact",
  "Core_Continuum_Input.evaluation_component_contract",
  "Core_Continuum_Input.evaluation_family_count",
  "Core_Continuum_Input.evaluation_family_other",
  "Core_Continuum_Input.evaluation_indices_exhaustive",
  "Core_Continuum_Input.evaluation_uses_source",
  "Core_Continuum_Input.granularity_components",
  "Core_Continuum_Input.granularity_tuple_components",
  "Core_Continuum_Input.no_rule_adds_nothing",
  "Core_Continuum_Input.record_representation.coordinate_candidate_map",
  "Core_Continuum_Input.record_representation.coordinate_candidate_topology",
  "Core_Continuum_Input.representation_base.stage_to_coordinate_factorization",
  "Core_Continuum_Input.step_count_one",
  "Core_Continuum_Input.tuple_generation_export",
  "Core_Continuum_Input.tuple_inputs_exact",
  "Core_Continuum_Input.typed_tuple_generation_export"
]\<close>
end
