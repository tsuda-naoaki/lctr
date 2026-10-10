theory Native_Metadata_01_075
imports
  "LCTR_Core_Law_Component_Charts.Core_Law_Component_Charts"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Component_Charts.native_component_chart.every_law_evaluation_covered",
  "Core_Law_Component_Charts.native_component_chart.native_coordinate_bijective",
  "Core_Law_Component_Charts.native_component_chart.native_input_curve",
  "Core_Law_Component_Charts.native_component_chart.native_output_curve",
  "Core_Law_Component_Charts.native_component_chart.native_side_curve",
  "Core_Law_Component_Charts.native_component_chart.same_law_values"
]\<close>
end
