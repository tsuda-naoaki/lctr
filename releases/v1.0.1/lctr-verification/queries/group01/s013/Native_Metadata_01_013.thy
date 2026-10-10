theory Native_Metadata_01_013
imports
  "LCTR_Core_Comparison_Failure_Witnesses.Core_Comparison_Failure_Witnesses"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Failure_Witnesses.factorization_failure",
  "Core_Comparison_Failure_Witnesses.native_comparison.mixed_nonfixed",
  "Core_Comparison_Failure_Witnesses.native_comparison.pure_nonfixed",
  "Core_Comparison_Failure_Witnesses.native_comparison.specified_nonfixed",
  "Core_Comparison_Failure_Witnesses.native_comparison.unrealizable_no_realization",
  "Core_Comparison_Failure_Witnesses.native_comparison.unrealizable_witness",
  "Core_Comparison_Failure_Witnesses.paired_comparison.pullback_mismatch",
  "Core_Comparison_Failure_Witnesses.paired_comparison.unsaturated_no_pullback",
  "Core_Comparison_Failure_Witnesses.paired_comparison.unsaturated_witness",
  "Core_Comparison_Failure_Witnesses.set_equality_failure",
  "Core_Comparison_Failure_Witnesses.source_collision",
  "Core_Comparison_Failure_Witnesses.unique_failure_cases"
]\<close>
end
