theory Native_Metadata_01_012
imports
  "LCTR_Core_Comparison_Failure.Core_Comparison_Failure"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Failure.comparison_incoming_exact",
  "Core_Comparison_Failure.first_and_last_conditions",
  "Core_Comparison_Failure.first_failure_partition",
  "Core_Comparison_Failure.first_index_unique",
  "Core_Comparison_Failure.incoming_from_prior_sat",
  "Core_Comparison_Failure.native_comparison.native_failure_partition",
  "Core_Comparison_Failure.native_comparison.native_signature_at_failure",
  "Core_Comparison_Failure.native_comparison.native_signature_component_sum",
  "Core_Comparison_Failure.native_comparison.native_signature_unique",
  "Core_Comparison_Failure.native_region_union",
  "Core_Comparison_Failure.native_regions_disjoint",
  "Core_Comparison_Failure.ready_comparison.comparison_failed_prefix",
  "Core_Comparison_Failure.ready_comparison.comparison_sat_prefix",
  "Core_Comparison_Failure.unrefined_region_signature"
]\<close>
end
