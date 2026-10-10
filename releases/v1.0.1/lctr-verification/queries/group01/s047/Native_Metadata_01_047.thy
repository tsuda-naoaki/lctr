theory Native_Metadata_01_047
imports
  "LCTR_Core_Engineering_Effects.Core_Engineering_Effects"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Engineering_Effects.admissibility_actual_site",
  "Core_Engineering_Effects.boundary_target_and_need",
  "Core_Engineering_Effects.envelope_component",
  "Core_Engineering_Effects.evaluation_effect_actual",
  "Core_Engineering_Effects.exact_requirement_component",
  "Core_Engineering_Effects.form_effect_actual",
  "Core_Engineering_Effects.missing_evaluation_is_not_failed",
  "Core_Engineering_Effects.missing_formation_is_unformed",
  "Core_Engineering_Effects.partition_component",
  "Core_Engineering_Effects.requirement_need_not_fail",
  "Core_Engineering_Effects.targets_stay_within_six_series",
  "Core_Engineering_Effects.unformed_boundary_input",
  "Core_Engineering_Effects.verified_has_reference"
]\<close>
end
