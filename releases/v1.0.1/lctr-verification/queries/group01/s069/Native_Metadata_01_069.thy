theory Native_Metadata_01_069
imports
  "LCTR_Core_Joint_Input_Data.Core_Joint_Input_Data"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Input_Data.bundle_context",
  "Core_Joint_Input_Data.bundle_datum",
  "Core_Joint_Input_Data.bundle_indices",
  "Core_Joint_Input_Data.bundle_roles",
  "Core_Joint_Input_Data.empty_relation_allowed",
  "Core_Joint_Input_Data.empty_value_relation",
  "Core_Joint_Input_Data.indexed_relation_domain",
  "Core_Joint_Input_Data.predicate_membership",
  "Core_Joint_Input_Data.predicate_value_unique",
  "Core_Joint_Input_Data.relation_domain",
  "Core_Joint_Input_Data.relation_not_forced_total",
  "Core_Joint_Input_Data.selected_index_exists",
  "Core_Joint_Input_Data.source_components"
]\<close>
end
