theory Native_Metadata_01_152
imports
  "LCTR_Core_Trajectory_Descent_Alignment.Core_Trajectory_Descent_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Trajectory_Descent_Alignment.domain_is_source_image",
  "Core_Trajectory_Descent_Alignment.empty_relation_domain",
  "Core_Trajectory_Descent_Alignment.generated_closure_descent",
  "Core_Trajectory_Descent_Alignment.generated_equivalence_least",
  "Core_Trajectory_Descent_Alignment.image_membership_iff",
  "Core_Trajectory_Descent_Alignment.missing_descent_control",
  "Core_Trajectory_Descent_Alignment.native_graph_trajectory",
  "Core_Trajectory_Descent_Alignment.trajectory_descent.descent_iff_exact_membership"
]\<close>
end
