theory Native_Metadata_01_092
imports
  "LCTR_Core_Localization_Bundle.Core_Localization_Bundle"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Localization_Bundle.assembled_domain_intersection",
  "Core_Localization_Bundle.assembled_independent_of_solution",
  "Core_Localization_Bundle.assembled_signature_is_minimal",
  "Core_Localization_Bundle.boundary_tokens_at_least",
  "Core_Localization_Bundle.boundary_tokens_only_approx",
  "Core_Localization_Bundle.domain_intersection",
  "Core_Localization_Bundle.interval_equals_initial_approx",
  "Core_Localization_Bundle.interval_within_approx",
  "Core_Localization_Bundle.localization_data_unique",
  "Core_Localization_Bundle.native_solution_family_unique",
  "Core_Localization_Bundle.no_boundary_no_burden",
  "Core_Localization_Bundle.no_boundary_no_tokens",
  "Core_Localization_Bundle.quantitative_interval"
]\<close>
end
