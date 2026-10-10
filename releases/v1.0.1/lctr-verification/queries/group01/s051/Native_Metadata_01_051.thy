theory Native_Metadata_01_051
imports
  "LCTR_Core_Exact_Input_Assembly.Core_Exact_Input_Assembly"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Exact_Input_Assembly.exact_structure.source_order_recovered",
  "Core_Exact_Input_Assembly.ordered_completion.local_global_same_source",
  "Core_Exact_Input_Assembly.paired_ordered_assembly.comparison_and_order_same_input",
  "Core_Exact_Input_Assembly.paired_ordered_assembly.comparison_injection_retained",
  "Core_Exact_Input_Assembly.paired_ordered_assembly.generated_order_no_extra_coordinate_input",
  "Core_Exact_Input_Assembly.paired_ordered_assembly.ordered_family_unique",
  "Core_Exact_Input_Assembly.same_arrivals",
  "Core_Exact_Input_Assembly.same_projection",
  "Core_Exact_Input_Assembly.same_quotient",
  "Core_Exact_Input_Assembly.same_transport"
]\<close>
end
