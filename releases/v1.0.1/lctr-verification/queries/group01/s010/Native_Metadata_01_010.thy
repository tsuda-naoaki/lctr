theory Native_Metadata_01_010
imports
  "LCTR_Core_Comparison_Alignment.Core_Comparison_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Alignment.canonical_comparison_partial_order",
  "Core_Comparison_Alignment.comparison_equivalence",
  "Core_Comparison_Alignment.comparison_loop_projection_criterion",
  "Core_Comparison_Alignment.comparison_order_separation",
  "Core_Comparison_Alignment.equal_recovery_comparison"
]\<close>
end
