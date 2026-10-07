theory Native_Metadata_01_143
imports
  "LCTR_Core_Series_Validity.Core_Series_Validity"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Series_Validity.completion_clears_failures",
  "Core_Series_Validity.completion_split",
  "Core_Series_Validity.native_audit_pass_iff_completion",
  "Core_Series_Validity.native_completion_iff_inputs",
  "Core_Series_Validity.no_failure_does_not_imply_completion",
  "Core_Series_Validity.profile_completion_iff",
  "Core_Series_Validity.profile_strict_scale_independent",
  "Core_Series_Validity.series_completion_iff",
  "Core_Series_Validity.validity_domain_intersection"
]\<close>
end
