theory Native_Metadata_01_064
imports
  "LCTR_Core_Generated_Law_Identity.Core_Generated_Law_Identity"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Generated_Law_Identity.carrier_bijection.base_coordinate_identity",
  "Core_Generated_Law_Identity.carrier_bijection.base_family_identity",
  "Core_Generated_Law_Identity.generated_law_change.coordinate_change_bijection",
  "Core_Generated_Law_Identity.generated_law_change.coordinate_change_on_source",
  "Core_Generated_Law_Identity.generated_law_change.coordinate_change_unique"
]\<close>
end
