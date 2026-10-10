theory Native_Metadata_01_048
imports
  "LCTR_Core_Engineering_Evidence.Core_Engineering_Evidence"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Engineering_Evidence.engineering_evidence.certificate_correspondence",
  "Core_Engineering_Evidence.engineering_evidence.condition_evidence_required",
  "Core_Engineering_Evidence.engineering_evidence.fail_iff_native_failed",
  "Core_Engineering_Evidence.engineering_evidence.failure_image_localized",
  "Core_Engineering_Evidence.engineering_evidence.measurements_typed",
  "Core_Engineering_Evidence.engineering_evidence.references_nonempty",
  "Core_Engineering_Evidence.engineering_evidence.relative_burden_unique",
  "Core_Engineering_Evidence.engineering_evidence.satisfied_target_is_not_failed",
  "Core_Engineering_Evidence.engineering_evidence.shared_reference_targets",
  "Core_Engineering_Evidence.engineering_evidence.six_series_locality",
  "Core_Engineering_Evidence.engineering_evidence.state_is_target_state",
  "Core_Engineering_Evidence.engineering_evidence.target_image_exact"
]\<close>
end
