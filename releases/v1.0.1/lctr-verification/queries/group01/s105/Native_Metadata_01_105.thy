theory Native_Metadata_01_105
imports
  "LCTR_Core_Native_State_Bridge.Core_Native_State_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_State_Bridge.canonical_recursion_unique",
  "Core_Native_State_Bridge.gate_and_state_cases",
  "Core_Native_State_Bridge.missing_input_unformed",
  "Core_Native_State_Bridge.off_domain_not_failed",
  "Core_Native_State_Bridge.state_section_recursion",
  "Core_Native_State_Bridge.strict_argument_recovery",
  "Core_Native_State_Bridge.strict_failed_recovery",
  "Core_Native_State_Bridge.strict_failed_scale_independent",
  "Core_Native_State_Bridge.strict_failed_typed",
  "Core_Native_State_Bridge.strict_state_scale_independent"
]\<close>
end
