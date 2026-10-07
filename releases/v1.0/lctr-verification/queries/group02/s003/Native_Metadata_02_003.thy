theory Native_Metadata_02_003
imports
  "LCTR_Core_Preorder_Alignment.Core_Preorder_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Preorder_Alignment.descent_is_necessary",
  "Core_Preorder_Alignment.empty_quotient",
  "Core_Preorder_Alignment.missing_descent_counterexample",
  "Core_Preorder_Alignment.missing_separation_counterexample",
  "Core_Preorder_Alignment.preorder_pullback",
  "Core_Preorder_Alignment.quotient_on_representatives",
  "Core_Preorder_Alignment.quotient_partial_order",
  "Core_Preorder_Alignment.quotient_preorder",
  "Core_Preorder_Alignment.quotient_relation_unique",
  "Core_Preorder_Alignment.source_induced_preorder"
]\<close>
end
