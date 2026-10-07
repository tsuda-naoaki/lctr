theory Native_Metadata_01_040
imports
  "LCTR_Core_Dynamics_Bundle.Core_Dynamics_Bundle"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Bundle.native_dynamics_bundle.curve_range_preserved",
  "Core_Dynamics_Bundle.native_dynamics_bundle.description_exists_unique",
  "Core_Dynamics_Bundle.native_dynamics_bundle.description_spec",
  "Core_Dynamics_Bundle.native_dynamics_bundle.description_unique",
  "Core_Dynamics_Bundle.native_dynamics_bundle.shared_input_exact",
  "Core_Dynamics_Bundle.native_dynamics_bundle.time_spec",
  "Core_Dynamics_Bundle.native_dynamics_bundle.time_unique",
  "Core_Dynamics_Bundle.native_dynamics_bundle.trajectory_spec",
  "Core_Dynamics_Bundle.native_dynamics_bundle.trajectory_unique",
  "Core_Dynamics_Bundle.native_dynamics_bundle.witness_exists_unique"
]\<close>
end
