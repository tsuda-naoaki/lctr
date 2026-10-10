theory Native_Metadata_01_160
imports
  "LCTR_Generic_Differential_Covariance.Generic_Differential_Covariance"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Generic_Differential_Covariance.differential_covariance",
  "Generic_Differential_Covariance.time_map_bijective",
  "Generic_Differential_Covariance.time_preserves_zeroth_value",
  "Generic_Differential_Covariance.time_relation_image",
  "Generic_Differential_Covariance.value_map_bijective",
  "Generic_Differential_Covariance.value_preserves_time_coordinate",
  "Generic_Differential_Covariance.value_relation_image"
]\<close>
end
