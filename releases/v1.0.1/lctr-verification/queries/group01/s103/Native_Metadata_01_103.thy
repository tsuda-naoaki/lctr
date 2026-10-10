theory Native_Metadata_01_103
imports
  "LCTR_Core_Native_Observables.Core_Native_Observables"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Observables.native_observable_curves.native_curve_local_value",
  "Core_Native_Observables.native_observables.actual_comparison_fiber_invariant",
  "Core_Native_Observables.native_observables.actual_projection_surjective",
  "Core_Native_Observables.native_observables.canonical_representative_value",
  "Core_Native_Observables.native_observables.canonical_unique",
  "Core_Native_Observables.native_observables.canonical_value_typed",
  "Core_Native_Observables.native_observables.local_change_compatibility",
  "Core_Native_Observables.native_observables.native_factor_exists_unique",
  "Core_Native_Observables.native_observables.range_representative_independence"
]\<close>
end
