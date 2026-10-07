theory Native_Metadata_02_001
imports
  "LCTR_Core_Audit_Tags.Core_Audit_Tags"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Audit_Tags.empty_reasons_preserve_payload",
  "Core_Audit_Tags.no_empty_reason_tag",
  "Core_Audit_Tags.nonempty_reasons_hide_payload",
  "Core_Audit_Tags.tag_transport.generated_tagged_transport",
  "Core_Audit_Tags.tag_transport.group_reasons_transport",
  "Core_Audit_Tags.tag_transport.reasons_transport",
  "Core_Audit_Tags.tag_transport.tagged_transport"
]\<close>
end
