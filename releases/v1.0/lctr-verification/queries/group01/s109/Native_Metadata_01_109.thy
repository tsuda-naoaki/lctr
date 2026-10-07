theory Native_Metadata_01_109
imports
  "LCTR_Core_Observable_Interfaces.Core_Observable_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Observable_Interfaces.raw_observables.change_commutes_iff",
  "Core_Observable_Interfaces.raw_observables.changed_domain_iff",
  "Core_Observable_Interfaces.raw_observables.changed_value_formula",
  "Core_Observable_Interfaces.raw_observables.changed_value_typed",
  "Core_Observable_Interfaces.raw_observables.common_value_formula",
  "Core_Observable_Interfaces.raw_observables.common_value_typed",
  "Core_Observable_Interfaces.raw_observables.descent_conditions_iff",
  "Core_Observable_Interfaces.raw_observables.local_state_formula",
  "Core_Observable_Interfaces.raw_observables.local_state_kernel",
  "Core_Observable_Interfaces.raw_observables.raw_comparison_fiber_invariant",
  "Core_Observable_Interfaces.raw_observables.raw_factor_exists_unique",
  "Core_Observable_Interfaces.raw_observables.raw_projection_surjective",
  "Core_Observable_Interfaces.trajectory_single_domain_iff"
]\<close>
end
