theory Native_Metadata_01_015
imports
  "LCTR_Core_Comparison_Scope.Core_Comparison_Scope"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Scope.all_conditions_iff_operative",
  "Core_Comparison_Scope.assigned_failure_equivalence",
  "Core_Comparison_Scope.comparison_series_exact",
  "Core_Comparison_Scope.failure_condition_equivalence",
  "Core_Comparison_Scope.native_failed_antichain_and_minimal",
  "Core_Comparison_Scope.native_failed_class_membership",
  "Core_Comparison_Scope.native_first_failure_unique",
  "Core_Comparison_Scope.native_series_partition"
]\<close>
end
