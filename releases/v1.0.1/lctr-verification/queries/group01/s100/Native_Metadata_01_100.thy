theory Native_Metadata_01_100
imports
  "LCTR_Core_Native_Law_Family.Core_Native_Law_Family"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Law_Family.all_conditions_exact",
  "Core_Native_Law_Family.ancestor_conditions_hold",
  "Core_Native_Law_Family.ancestor_sets",
  "Core_Native_Law_Family.condition_dependency",
  "Core_Native_Law_Family.condition_vector_exact",
  "Core_Native_Law_Family.roots_exact"
]\<close>
end
