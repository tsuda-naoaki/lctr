theory Native_Metadata_01_125
imports
  "LCTR_Core_Reception_Input.Core_Reception_Input"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Reception_Input.comparison_role_exact",
  "Core_Reception_Input.restriction_exact",
  "Core_Reception_Input.restriction_partial_order",
  "Core_Reception_Input.source_role_exact",
  "Core_Reception_Input.source_role_injective",
  "Core_Reception_Input.total_reception_decomposition",
  "Core_Reception_Input.total_reception_distinct_nodes"
]\<close>
end
