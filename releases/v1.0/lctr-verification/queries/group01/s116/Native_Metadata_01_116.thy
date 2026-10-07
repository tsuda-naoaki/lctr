theory Native_Metadata_01_116
imports
  "LCTR_Core_Paired_Comparison.Core_Paired_Comparison"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Paired_Comparison.paired_comparison.canonical_relation_least",
  "Core_Paired_Comparison.paired_comparison.canonical_relation_pullback",
  "Core_Paired_Comparison.paired_comparison.canonical_relation_typed",
  "Core_Paired_Comparison.paired_comparison.canonical_relation_unique_minimal",
  "Core_Paired_Comparison.paired_comparison.empty_relation",
  "Core_Paired_Comparison.paired_comparison.local_pair_projection_injective",
  "Core_Paired_Comparison.paired_comparison.paired_equivalence",
  "Core_Paired_Comparison.paired_comparison.projection_kernel",
  "Core_Paired_Comparison.paired_comparison.saturation_necessary_for_pullback",
  "Core_Paired_Comparison.paired_comparison.source_relation_pullback"
]\<close>
end
