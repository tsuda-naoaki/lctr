theory Native_Metadata_05_001
imports
  "LCTR_Core_Audit_Data.Core_Audit_Data"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Audit_Data.approximation_evidence_selected",
  "Core_Audit_Data.certificate_does_not_change_computation",
  "Core_Audit_Data.certificate_fields_retained",
  "Core_Audit_Data.different_certificates_remain_distinct",
  "Core_Audit_Data.formed_branch_exact",
  "Core_Audit_Data.input_series_exact",
  "Core_Audit_Data.readout_certificate_exact",
  "Core_Audit_Data.readout_data_exact",
  "Core_Audit_Data.strict_evidence_scale_independent",
  "Core_Audit_Data.typed_report_unique",
  "Core_Audit_Data.unformed_branch_exact"
]\<close>
end
