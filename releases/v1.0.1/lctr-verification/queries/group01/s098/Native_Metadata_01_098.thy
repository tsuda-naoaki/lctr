theory Native_Metadata_01_098
imports
  "LCTR_Core_Native_Law_Components.Core_Native_Law_Components"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Law_Components.empty_index_values_unique",
  "Core_Native_Law_Components.native_law_context.candidate_relation_typed",
  "Core_Native_Law_Components.native_law_context.evaluation_tuple_components",
  "Core_Native_Law_Components.native_law_context.evaluation_tuple_domain_typed",
  "Core_Native_Law_Components.native_law_context.generated_membership_contract",
  "Core_Native_Law_Components.native_law_context.generated_value_components",
  "Core_Native_Law_Components.native_law_context.individual_input_typed",
  "Core_Native_Law_Components.native_law_context.native_common_valid_contract",
  "Core_Native_Law_Components.native_law_context.native_partial_output"
]\<close>
end
