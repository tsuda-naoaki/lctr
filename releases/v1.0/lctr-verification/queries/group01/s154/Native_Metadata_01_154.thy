theory Native_Metadata_01_154
imports
  "LCTR_Core_Transported_Native_Jets.Core_Transported_Native_Jets"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Transported_Native_Jets.native_jet_data_exact",
  "Core_Transported_Native_Jets.native_real_component_chart.native_law_reindex_jet_exact(1)",
  "Core_Transported_Native_Jets.native_real_component_chart.native_law_reindex_jet_exact(2)",
  "Core_Transported_Native_Jets.native_real_component_chart.native_law_reindex_jet_exact(3)",
  "Core_Transported_Native_Jets.real_transported_atlas.realization_in_value_chart",
  "Core_Transported_Native_Jets.real_transported_atlas.transported_jet_membership",
  "Core_Transported_Native_Jets.real_transported_atlas.transported_regularity",
  "Core_Transported_Native_Jets.source_theta_value",
  "Core_Transported_Native_Jets.transported_coordinate_atlas.curve_at_transported_coordinate",
  "Core_Transported_Native_Jets.transported_extension_fixed",
  "Core_Transported_Native_Jets.transported_jet_equal"
]\<close>
end
