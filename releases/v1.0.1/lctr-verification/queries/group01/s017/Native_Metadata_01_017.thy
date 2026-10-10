theory Native_Metadata_01_017
imports
  "LCTR_Core_Configuration_Comparison.Core_Configuration_Comparison"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Configuration_Comparison.configuration_comparison.joint_graph_exact",
  "Core_Configuration_Comparison.configuration_comparison.l5_from_configuration",
  "Core_Configuration_Comparison.configuration_comparison.native_local_injective",
  "Core_Configuration_Comparison.configuration_comparison.native_output_unique",
  "Core_Configuration_Comparison.configuration_comparison.native_source_relation_pullback",
  "Core_Configuration_Comparison.configuration_comparison.remaining_iff_operative",
  "Core_Configuration_Comparison.configuration_comparison.transport_partial_injection",
  "Core_Configuration_Comparison.configuration_comparison.transport_preserved",
  "Core_Configuration_Comparison.configuration_comparison_seed.arrival_preserved",
  "Core_Configuration_Comparison.configuration_comparison_seed.l2_exact",
  "Core_Configuration_Comparison.configuration_comparison_seed.relations_preserved"
]\<close>
end
