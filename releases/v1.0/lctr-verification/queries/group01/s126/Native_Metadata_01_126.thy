theory Native_Metadata_01_126
imports
  "LCTR_Core_Record_Burden.Core_Record_Burden"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Record_Burden.bulk_omits_communication",
  "Core_Record_Burden.following_includes_communication",
  "Core_Record_Burden.record_burden.burden_equal_iff_delta_empty",
  "Core_Record_Burden.record_burden.no_failed_evidence_no_burden",
  "Core_Record_Burden.record_burden.no_failed_evidence_no_tokens",
  "Core_Record_Burden.record_burden.one_sided_separation",
  "Core_Record_Burden.record_burden.singleton_burden_included",
  "Core_Record_Burden.record_burden.tag_difference_alone_not_burden_difference",
  "Core_Record_Burden.record_burden.token_target_locality",
  "Core_Record_Burden.record_burden.token_witness",
  "Core_Record_Burden.record_burden.two_sided_incomparability",
  "Core_Record_Burden.record_burden.witness_measurement_typed",
  "Core_Record_Burden.tag_domains"
]\<close>
end
