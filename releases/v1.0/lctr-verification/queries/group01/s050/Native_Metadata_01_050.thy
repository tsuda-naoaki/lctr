theory Native_Metadata_01_050
imports
  "LCTR_Core_Exact_Completion.Core_Exact_Completion"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Exact_Completion.exact_structure.canonical_order_unique",
  "Core_Exact_Completion.exact_structure.conventional_time_coordinate_freedom",
  "Core_Exact_Completion.ordered_completion.canonical_ordered_bundle_exists_unique",
  "Core_Exact_Completion.ordered_completion.conventional_time_factor",
  "Core_Exact_Completion.ordered_completion.generated_ordered_valid",
  "Core_Exact_Completion.ordered_completion.ordered_output_unique",
  "Core_Exact_Completion.paired_comparison.native_conditions_give_comparison_output",
  "Core_Exact_Completion.paired_comparison.native_master_condition"
]\<close>
end
