theory Native_Metadata_01_052
imports
  "LCTR_Core_Exact_Structure.Core_Exact_Structure"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Exact_Structure.exact_structure.actual_global_quotient_linear",
  "Core_Exact_Structure.exact_structure.actual_local_chart_contract",
  "Core_Exact_Structure.exact_structure.actual_local_quotient_linear",
  "Core_Exact_Structure.exact_structure.canonical_order_representatives",
  "Core_Exact_Structure.exact_structure.canonical_partial_order",
  "Core_Exact_Structure.exact_structure.chosen_representation_compatibility",
  "Core_Exact_Structure.exact_structure.global_implies_local_inc",
  "Core_Exact_Structure.exact_structure.local_global_chart_commutes",
  "Core_Exact_Structure.exact_structure.local_global_commutes",
  "Core_Exact_Structure.exact_structure.local_global_injective",
  "Core_Exact_Structure.exact_structure.local_global_order",
  "Core_Exact_Structure.exact_structure.receive_onto",
  "Core_Exact_Structure.exact_structure.represented_kernel",
  "Core_Exact_Structure.exact_structure.represented_order_pullback",
  "Core_Exact_Structure.exact_structure.strict_part_contract"
]\<close>
end
