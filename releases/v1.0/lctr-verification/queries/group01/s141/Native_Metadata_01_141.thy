theory Native_Metadata_01_141
imports
  "LCTR_Core_Scope_Input_Interfaces.Core_Scope_Input_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Scope_Input_Interfaces.restriction_membership",
  "Core_Scope_Input_Interfaces.restriction_subtype",
  "Core_Scope_Input_Interfaces.shared_carrier_distinct_sources",
  "Core_Scope_Input_Interfaces.support_selection"
]\<close>
end
