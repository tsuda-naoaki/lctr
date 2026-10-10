theory Native_Metadata_01_087
imports
  "LCTR_Core_Local_Charts.Core_Local_Charts"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Local_Charts.coordinate_atlas.coordinate_curve_generated",
  "Core_Local_Charts.coordinate_atlas.curve_unique",
  "Core_Local_Charts.coordinate_atlas.generation_at_every_time",
  "Core_Local_Charts.coordinate_atlas.inverse_agrees_with_time_chart",
  "Core_Local_Charts.coordinate_atlas.inverse_left",
  "Core_Local_Charts.coordinate_atlas.inverse_right",
  "Core_Local_Charts.coordinate_atlas.joint_domain_coverage",
  "Core_Local_Charts.coordinate_atlas.side_curve_generated",
  "Core_Local_Charts.coordinate_atlas.time_coordinate_bijective",
  "Core_Local_Charts.coordinate_atlas.time_value_injective"
]\<close>
end
