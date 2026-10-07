theory Native_Metadata_01_124
imports
  "LCTR_Core_Raw_Localization_Interfaces.Core_Raw_Localization_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Raw_Localization_Interfaces.approx_failed_membership",
  "Core_Raw_Localization_Interfaces.approx_localization",
  "Core_Raw_Localization_Interfaces.approximation_downward",
  "Core_Raw_Localization_Interfaces.approximation_membership",
  "Core_Raw_Localization_Interfaces.empty_family",
  "Core_Raw_Localization_Interfaces.family_intersection",
  "Core_Raw_Localization_Interfaces.localization_antichain",
  "Core_Raw_Localization_Interfaces.localization_subset",
  "Core_Raw_Localization_Interfaces.nontrans_exact",
  "Core_Raw_Localization_Interfaces.nontrans_iff_not_transitive",
  "Core_Raw_Localization_Interfaces.section_membership",
  "Core_Raw_Localization_Interfaces.split_components",
  "Core_Raw_Localization_Interfaces.split_decomposition",
  "Core_Raw_Localization_Interfaces.split_empty",
  "Core_Raw_Localization_Interfaces.state_distinct",
  "Core_Raw_Localization_Interfaces.state_exhaustive",
  "Core_Raw_Localization_Interfaces.strict_failed_membership",
  "Core_Raw_Localization_Interfaces.strict_localization",
  "Core_Raw_Localization_Interfaces.valid_membership"
]\<close>
end
