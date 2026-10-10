theory Native_Metadata_01_153
imports
  "LCTR_Core_Transported_Law_Charts.Core_Transported_Law_Charts"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Transported_Law_Charts.native_component_chart.transported_atlas_input_is_law_input",
  "Core_Transported_Law_Charts.native_component_chart.transported_atlas_output_is_law_output",
  "Core_Transported_Law_Charts.native_component_chart.transported_native_curve_agrees",
  "Core_Transported_Law_Charts.same_transported_input",
  "Core_Transported_Law_Charts.same_transported_output",
  "Core_Transported_Law_Charts.transported_coordinate_atlas.joint_lift_inverse",
  "Core_Transported_Law_Charts.transported_coordinate_atlas.joint_unlift_inverse",
  "Core_Transported_Law_Charts.transported_coordinate_atlas.native_curve_preserved",
  "Core_Transported_Law_Charts.transported_coordinate_atlas.numeric_domain_preserved",
  "Core_Transported_Law_Charts.transported_coordinate_atlas.numeric_time_preserved"
]\<close>
end
