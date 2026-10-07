theory Native_Metadata_01_093
imports
  "LCTR_Core_Native_Charts.Core_Native_Charts"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Charts.exact_structure.actual_chart_change_identity",
  "Core_Native_Charts.exact_structure.actual_chart_change_inverse",
  "Core_Native_Charts.exact_structure.actual_chart_change_order",
  "Core_Native_Charts.exact_structure.actual_chart_composition",
  "Core_Native_Charts.exact_structure.actual_representation_contract",
  "Core_Native_Charts.exact_structure.actual_triple_cocycle",
  "Core_Native_Charts.exact_structure.global_inc_equivalence",
  "Core_Native_Charts.exact_structure.global_strict_invariance",
  "Core_Native_Charts.exact_structure.local_global_inc_restriction",
  "Core_Native_Charts.exact_structure.local_inc_equivalence",
  "Core_Native_Charts.exact_structure.local_strict_invariance",
  "Core_Native_Charts.order_pair.reversed_chart_is_inverse",
  "Core_Native_Charts.quotient_embedding_composition",
  "Core_Native_Charts.reverse_input_commutes"
]\<close>
end
