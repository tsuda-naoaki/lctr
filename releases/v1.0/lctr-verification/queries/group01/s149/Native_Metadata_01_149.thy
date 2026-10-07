theory Native_Metadata_01_149
imports
  "LCTR_Core_Three_Layer_Synthesis.Core_Three_Layer_Synthesis"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Three_Layer_Synthesis.differential_conditions_keep_native_domains",
  "Core_Three_Layer_Synthesis.native_dynamics_bundle.dynamics_every_embedding",
  "Core_Three_Layer_Synthesis.native_dynamics_bundle.law_cores_all_embeddings",
  "Core_Three_Layer_Synthesis.native_dynamics_bundle.same_law_all_embeddings",
  "Core_Three_Layer_Synthesis.native_dynamics_bundle.same_reference_differential_objects",
  "Core_Three_Layer_Synthesis.native_dynamics_bundle.transported_core_exists_unique",
  "Core_Three_Layer_Synthesis.native_three_layers.cumulative_same_input",
  "Core_Three_Layer_Synthesis.native_three_layers.differential_equivalence",
  "Core_Three_Layer_Synthesis.native_three_layers.dynamics_equivalence",
  "Core_Three_Layer_Synthesis.native_three_layers.law_equivalence"
]\<close>
end
