theory Native_Metadata_01_165
imports
  "LCTR_Native_Differential_Synthesis_Alignment.Native_Differential_Synthesis_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Native_Differential_Synthesis_Alignment.native_differential_synthesis(1)",
  "Native_Differential_Synthesis_Alignment.native_differential_synthesis(2)",
  "Native_Differential_Synthesis_Alignment.native_flat_jet_membership",
  "Native_Differential_Synthesis_Alignment.native_generated_jet_membership",
  "Native_Differential_Synthesis_Alignment.native_time_relation_image",
  "Native_Differential_Synthesis_Alignment.native_value_relation_image(1)",
  "Native_Differential_Synthesis_Alignment.native_value_relation_image(2)",
  "Native_Differential_Synthesis_Alignment.native_value_relation_image(3)",
  "Native_Differential_Synthesis_Alignment.native_value_relation_image(4)",
  "Native_Differential_Synthesis_Alignment.native_value_relation_image(5)",
  "Native_Differential_Synthesis_Alignment.native_zeroth_values",
  "Native_Differential_Synthesis_Alignment.same_law_objects_every_representation",
  "Native_Differential_Synthesis_Alignment.time_change_zeroth_value",
  "Native_Differential_Synthesis_Alignment.time_order_isomorphism_unique"
]\<close>
end
