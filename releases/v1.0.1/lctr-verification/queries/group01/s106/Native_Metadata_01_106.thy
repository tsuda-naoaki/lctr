theory Native_Metadata_01_106
imports
  "LCTR_Core_Native_Time_Conditions.Core_Native_Time_Conditions"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Time_Conditions.coordinate_overlaps.bound_time_maps_unique",
  "Core_Native_Time_Conditions.coordinate_overlaps.rep_ambient_coordinates",
  "Core_Native_Time_Conditions.coordinate_overlaps.rep_change_from_actual_time_map",
  "Core_Native_Time_Conditions.coordinate_overlaps.rep_cov_independent_of_certificate",
  "Core_Native_Time_Conditions.coordinate_overlaps.rep_domain_formula",
  "Core_Native_Time_Conditions.coordinate_overlaps.rep_relation_restriction_image",
  "Core_Native_Time_Conditions.coordinate_overlaps.rep_time_change_preserves_value"
]\<close>
end
