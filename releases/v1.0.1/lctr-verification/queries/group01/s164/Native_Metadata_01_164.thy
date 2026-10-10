theory Native_Metadata_01_164
imports
  "LCTR_Native_Atlas_Certificates.Native_Atlas_Certificates"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Native_Atlas_Certificates.native_atlas_certificates.diff1_has_actual_changes",
  "Native_Atlas_Certificates.native_atlas_certificates.diff4_false_outside",
  "Native_Atlas_Certificates.native_atlas_certificates.diff4_requires_diff1",
  "Native_Atlas_Certificates.native_atlas_certificates.diff4_restricts",
  "Native_Atlas_Certificates.native_atlas_certificates.regular_time_domains_open",
  "Native_Atlas_Certificates.native_atlas_certificates.regular_value_domains_open",
  "Native_Atlas_Certificates.native_atlas_certificates.regular_value_maps_unique",
  "Native_Atlas_Certificates.native_atlas_certificates.time_ambient_preserves_coordinates",
  "Native_Atlas_Certificates.native_atlas_certificates.value_ambient_preserves_coordinates",
  "Native_Atlas_Certificates.native_atlas_certificates.value_cov_independent_of_certificate",
  "Native_Atlas_Certificates.value_relation_restriction_image(1)",
  "Native_Atlas_Certificates.value_relation_restriction_image(2)"
]\<close>
end
