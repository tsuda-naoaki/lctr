theory Native_Metadata_01_167
imports
  "LCTR_Native_Flatten_Final.Native_Flatten_Final"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Native_Flatten_Final.derivatives_preserved",
  "Native_Flatten_Final.flatten_actual_jet(1)",
  "Native_Flatten_Final.flatten_actual_jet(2)",
  "Native_Flatten_Final.flatten_actual_jet(3)",
  "Native_Flatten_Final.flatten_inverse",
  "Native_Flatten_Final.flattened_relation_membership",
  "Native_Flatten_Final.flattened_relation_recovered",
  "Native_Flatten_Final.jet_flatten_derivative_order",
  "Native_Flatten_Final.numeric_time_preserved",
  "Native_Flatten_Final.smoothness_preserved",
  "Native_Flatten_Final.unflatten_inverse"
]\<close>
end
