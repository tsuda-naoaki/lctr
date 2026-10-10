theory Native_Metadata_01_136
imports
  "LCTR_Core_Representation_Failure.Core_Representation_Failure"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Representation_Failure.comparison_failure_blocks_representation",
  "Core_Representation_Failure.comparison_success",
  "Core_Representation_Failure.generation_boundary",
  "Core_Representation_Failure.incoming_prefix",
  "Core_Representation_Failure.native_representation.all_conditions_pass_no_failure",
  "Core_Representation_Failure.native_representation.domain_separation",
  "Core_Representation_Failure.native_representation.native_failed_prefix",
  "Core_Representation_Failure.native_representation.native_generation_boundary",
  "Core_Representation_Failure.native_representation.native_localization",
  "Core_Representation_Failure.native_representation.native_refinement_monotonicity",
  "Core_Representation_Failure.native_representation.native_region_union",
  "Core_Representation_Failure.native_representation.native_regions_disjoint",
  "Core_Representation_Failure.native_representation.outside_has_no_failed_representation",
  "Core_Representation_Failure.native_representation.signature_at_failure",
  "Core_Representation_Failure.native_representation.signature_one_hot",
  "Core_Representation_Failure.native_representation.signature_token_correspondence",
  "Core_Representation_Failure.native_representation.token_region_correspondence",
  "Core_Representation_Failure.ready_representation.representation_failed_prefix",
  "Core_Representation_Failure.ready_representation.representation_sat_prefix",
  "Core_Representation_Failure.repr_first_failure_partition",
  "Core_Representation_Failure.repr_first_index_unique",
  "Core_Representation_Failure.representation_incoming_exact",
  "Core_Representation_Failure.representation_refinement.native_conditional_child_partition",
  "Core_Representation_Failure.representation_refinement.native_refinement_coverage"
]\<close>
end
