theory Native_Metadata_01_016
imports
  "LCTR_Core_Comparison_Stage.Core_Comparison_Stage"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Stage.paired_comparison.faithful_relation_requires_saturation",
  "Core_Comparison_Stage.paired_comparison.generated_local_injective",
  "Core_Comparison_Stage.paired_comparison.generated_local_pullback",
  "Core_Comparison_Stage.paired_comparison.generated_loop_identity",
  "Core_Comparison_Stage.paired_comparison.generated_pair_injective",
  "Core_Comparison_Stage.paired_comparison.generated_relation_least",
  "Core_Comparison_Stage.paired_comparison.generated_source_pullback",
  "Core_Comparison_Stage.paired_comparison.generated_valid",
  "Core_Comparison_Stage.paired_comparison.output_unique",
  "Core_Comparison_Stage.paired_comparison.unique_generated_output",
  "Core_Comparison_Stage.paired_comparison.valid_output_requires_realizability"
]\<close>
end
