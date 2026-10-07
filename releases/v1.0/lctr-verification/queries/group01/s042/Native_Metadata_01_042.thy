theory Native_Metadata_01_042
imports
  "LCTR_Core_Dynamics_Factors_Alignment.Core_Dynamics_Factors_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Factors_Alignment.canonical_projection_class",
  "Core_Dynamics_Factors_Alignment.canonical_projection_surjective",
  "Core_Dynamics_Factors_Alignment.canonical_source_order_preserved",
  "Core_Dynamics_Factors_Alignment.dynamics_factor_pair.native_factor_pair_exists_unique",
  "Core_Dynamics_Factors_Alignment.native_generated_partial_order",
  "Core_Dynamics_Factors_Alignment.native_order_minimality",
  "Core_Dynamics_Factors_Alignment.source_native_factor_pair",
  "Core_Dynamics_Factors_Alignment.trajectory_factor_image"
]\<close>
end
