theory Native_Metadata_01_028
imports
  "LCTR_Core_Continuum_Native_Records_Aligned.Core_Continuum_Native_Records"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Native_Records.record_codes.empty_source_no_collision",
  "Core_Continuum_Native_Records.record_codes.extra_collision_requires_identification",
  "Core_Continuum_Native_Records.record_codes.injective_mapping_preserves_collision",
  "Core_Continuum_Native_Records.record_codes.native_collision",
  "Core_Continuum_Native_Records.record_codes.native_domains",
  "Core_Continuum_Native_Records.record_codes.native_image",
  "Core_Continuum_Native_Records.record_codes.native_pair_records",
  "Core_Continuum_Native_Records.record_codes.native_separation_defect",
  "Core_Continuum_Native_Records.record_codes.native_state_records",
  "Core_Continuum_Native_Records.record_codes.native_time_records",
  "Core_Continuum_Native_Records.record_codes.pair_domain_has_source",
  "Core_Continuum_Native_Records.record_codes.pair_record_nonempty",
  "Core_Continuum_Native_Records.record_codes.unmapped_codes_collision"
]\<close>
end
