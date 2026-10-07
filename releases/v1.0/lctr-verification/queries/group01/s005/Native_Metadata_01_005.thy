theory Native_Metadata_01_005
imports
  "LCTR_Core_Approximate_Boundary.Core_Approximate_Boundary"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Approximate_Boundary.failure_implies_noncompletion",
  "Core_Approximate_Boundary.initial_completion_interval",
  "Core_Approximate_Boundary.least_failure_after_boundary",
  "Core_Approximate_Boundary.least_failure_case",
  "Core_Approximate_Boundary.least_failure_unique",
  "Core_Approximate_Boundary.least_scales_equal_if_failure_detected",
  "Core_Approximate_Boundary.native_all_scales_valid",
  "Core_Approximate_Boundary.native_boundary_nonzero_signature",
  "Core_Approximate_Boundary.native_maximal_interval",
  "Core_Approximate_Boundary.native_scale_input.native_completion_threshold",
  "Core_Approximate_Boundary.native_scale_input.native_saturation_is_valid",
  "Core_Approximate_Boundary.native_validity_initial",
  "Core_Approximate_Boundary.scale_sets_equal_if_failure_detected",
  "Core_Approximate_Boundary.unformed_scale_separation_control"
]\<close>
end
