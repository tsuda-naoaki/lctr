theory Native_Metadata_01_101
imports
  "LCTR_Core_Native_Law_Generation.Core_Native_Law_Generation"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Law_Generation.native_law_context.actual_trajectory_representative",
  "Core_Native_Law_Generation.native_law_context.common_evaluation_source_values",
  "Core_Native_Law_Generation.native_law_context.common_generated_representability",
  "Core_Native_Law_Generation.native_law_context.empty_trajectory_rejects_law_conditions",
  "Core_Native_Law_Generation.native_law_context.generated_preimage_unique",
  "Core_Native_Law_Generation.native_law_generation_transport.transported_law_generation"
]\<close>
end
