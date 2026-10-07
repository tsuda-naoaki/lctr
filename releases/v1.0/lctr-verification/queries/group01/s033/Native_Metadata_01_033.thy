theory Native_Metadata_01_033
imports
  "LCTR_Core_Detector_Source_Bridge.Core_Detector_Source_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Detector_Source_Bridge.content_embedding_injective",
  "Core_Detector_Source_Bridge.content_order_exact",
  "Core_Detector_Source_Bridge.equal_counter_distinct_content",
  "Core_Detector_Source_Bridge.missing_identity_control",
  "Core_Detector_Source_Bridge.pairing_retains_identity",
  "Core_Detector_Source_Bridge.record_identity_exact",
  "Core_Detector_Source_Bridge.recovery_preserves_record_content"
]\<close>
end
