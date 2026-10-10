theory Native_Metadata_01_008
imports
  "LCTR_Core_Carrier_Patterns.Core_Carrier_Patterns"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Carrier_Patterns.body_abstraction_retained",
  "Core_Carrier_Patterns.body_independent_of_realization",
  "Core_Carrier_Patterns.body_pair_distinct",
  "Core_Carrier_Patterns.carrier_condition_from_specified_values",
  "Core_Carrier_Patterns.carrier_condition_locality",
  "Core_Carrier_Patterns.no_distribution_without_communication",
  "Core_Carrier_Patterns.physical_identity_does_not_merge_roles",
  "Core_Carrier_Patterns.realization_domain_exact",
  "Core_Carrier_Patterns.role_index_preserved",
  "Core_Carrier_Patterns.role_typed_combination"
]\<close>
end
