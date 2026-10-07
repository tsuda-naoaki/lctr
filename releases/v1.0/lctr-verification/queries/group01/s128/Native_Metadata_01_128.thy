theory Native_Metadata_01_128
imports
  "LCTR_Core_Record_Codes_Aligned.Core_Record_Codes"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Record_Codes.record_codes.empty_source_records",
  "Core_Record_Codes.record_codes.pair_records_typed",
  "Core_Record_Codes.record_codes.pair_source_membership",
  "Core_Record_Codes.record_codes.projected_record_values_typed",
  "Core_Record_Codes.record_codes.record_code_components",
  "Core_Record_Codes.record_codes.record_values_not_forced_single",
  "Core_Record_Codes.record_codes.state_projection_exact",
  "Core_Record_Codes.record_codes.time_projection_exact"
]\<close>
end
