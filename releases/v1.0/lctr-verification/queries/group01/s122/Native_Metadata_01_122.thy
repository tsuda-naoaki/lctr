theory Native_Metadata_01_122
imports
  "LCTR_Core_Raw_Canonical_Observables.Core_Raw_Canonical_Observables"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Raw_Canonical_Observables.raw_observables.canonical_representative_value",
  "Core_Raw_Canonical_Observables.raw_observables.canonical_unique",
  "Core_Raw_Canonical_Observables.raw_observables.canonical_value_typed",
  "Core_Raw_Canonical_Observables.raw_observables.local_change_compatibility",
  "Core_Raw_Canonical_Observables.raw_observables.range_representative_independence",
  "Core_Raw_Canonical_Observables.raw_observables.whole_family_representation"
]\<close>
end
