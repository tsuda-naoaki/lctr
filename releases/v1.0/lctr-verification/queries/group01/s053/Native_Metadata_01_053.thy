theory Native_Metadata_01_053
imports
  "LCTR_Core_External_Time_Uses.Core_External_Time_Uses"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_External_Time_Uses.external_time_audit.actual_site_identifies_target",
  "Core_External_Time_Uses.external_time_audit.empty_allows_only_metadata_uses",
  "Core_External_Time_Uses.external_time_audit.empty_iff_no_actual_sites",
  "Core_External_Time_Uses.external_time_audit.every_actual_site_is_flagged",
  "Core_External_Time_Uses.external_time_audit.metadata_use_has_no_premise_site",
  "Core_External_Time_Uses.external_time_audit.violation_iff_actual_site",
  "Core_External_Time_Uses.metadata_tag_alone_does_not_certify",
  "Core_External_Time_Uses.native_states_depend_on_typed_inputs"
]\<close>
end
