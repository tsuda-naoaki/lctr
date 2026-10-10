theory Native_Metadata_03_001
imports
  "LCTR_Core_Audit_Groups.Core_Audit_Groups"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Audit_Groups.audit_fail_exact",
  "Core_Audit_Groups.audit_pass_exact",
  "Core_Audit_Groups.decode_priority",
  "Core_Audit_Groups.group_attained",
  "Core_Audit_Groups.group_attains_priority",
  "Core_Audit_Groups.group_maximum",
  "Core_Audit_Groups.group_nonempty",
  "Core_Audit_Groups.group_status_unique",
  "Core_Audit_Groups.group_transport.group_status_covariance",
  "Core_Audit_Groups.group_transport.group_tokens_image",
  "Core_Audit_Groups.native_failed_fiber",
  "Core_Audit_Groups.native_pass_iff",
  "Core_Audit_Groups.priority_groupStatus"
]\<close>
end
