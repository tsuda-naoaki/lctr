theory Native_Metadata_01_079
imports
  "LCTR_Core_Law_Differential_Bundle.Core_Law_Differential_Bundle"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Differential_Bundle.native_dynamics_bundle.differential_curve_typed",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.differential_exists_unique",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.differential_same_dynamics",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.differential_spec",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.differential_unique",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.differential_with_law_conditions",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.law_core_exists_unique",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.law_core_same_source",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.law_core_validity",
  "Core_Law_Differential_Bundle.native_dynamics_bundle.typed_law_curve_agrees"
]\<close>
end
