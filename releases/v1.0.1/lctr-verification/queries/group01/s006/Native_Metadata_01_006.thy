theory Native_Metadata_01_006
imports
  "LCTR_Core_Audit_State_Transport.Core_Audit_State_Transport"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Audit_State_Transport.audit_failure_exact",
  "Core_Audit_State_Transport.audit_transport.audit_at_covariance",
  "Core_Audit_State_Transport.audit_transport.audit_fiber_image",
  "Core_Audit_State_Transport.audit_transport.audit_state_transport",
  "Core_Audit_State_Transport.audit_transport.group_priority_covariance",
  "Core_Audit_State_Transport.audit_transport.indeterminate_signature_covariance",
  "Core_Audit_State_Transport.audit_transport.predecessors_pass_iff",
  "Core_Audit_State_Transport.audit_transport.recursion_pullback",
  "Core_Audit_State_Transport.audit_transport.state_covariance",
  "Core_Audit_State_Transport.blocked_and_unformed_distinct",
  "Core_Audit_State_Transport.missing_formation_not_failure",
  "Core_Audit_State_Transport.priority_injective"
]\<close>
end
