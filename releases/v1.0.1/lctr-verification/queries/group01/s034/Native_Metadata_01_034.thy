theory Native_Metadata_01_034
imports
  "LCTR_Core_Differential_Execution.Core_Differential_Execution"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Differential_Execution.atlas_only_failure_execution",
  "Core_Differential_Execution.control_profiles_have_native_inputs",
  "Core_Differential_Execution.outside_differential_passes",
  "Core_Differential_Execution.profile_truth_is_native",
  "Core_Differential_Execution.simultaneous_pair_execution",
  "Core_Differential_Execution.simultaneous_three_with_blocked_descendant",
  "Core_Differential_Execution.test_failure",
  "Core_Differential_Execution.test_ready_and_satisfaction"
]\<close>
end
