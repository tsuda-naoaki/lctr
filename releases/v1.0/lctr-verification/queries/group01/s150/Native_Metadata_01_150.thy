theory Native_Metadata_01_150
imports
  "LCTR_Core_Time_Jet_Changes.Core_Time_Jet_Changes"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Time_Jet_Changes.base_and_fiber_bijective",
  "Core_Time_Jet_Changes.full_domain_relation_image",
  "Core_Time_Jet_Changes.lift_bijective",
  "Core_Time_Jet_Changes.lift_composition",
  "Core_Time_Jet_Changes.lift_identity",
  "Core_Time_Jet_Changes.lift_left_inverse",
  "Core_Time_Jet_Changes.lift_unique",
  "Core_Time_Jet_Changes.time_jet_full_domain_bijective"
]\<close>
end
