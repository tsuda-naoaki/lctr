theory Native_Metadata_01_067
imports
  "LCTR_Core_Joint_Condition_Routes.Core_Joint_Condition_Routes"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Condition_Routes.native_joint_law.common_time_route",
  "Core_Joint_Condition_Routes.native_joint_law.individual_trajectory_route",
  "Core_Joint_Condition_Routes.native_joint_law.joint_descent_route",
  "Core_Joint_Condition_Routes.native_joint_law.joint_differential_minimal_route",
  "Core_Joint_Condition_Routes.native_joint_law.joint_differential_missing_domain",
  "Core_Joint_Condition_Routes.native_joint_law.joint_differential_requires_same_law",
  "Core_Joint_Condition_Routes.native_joint_law.joint_differential_route",
  "Core_Joint_Condition_Routes.native_joint_law.joint_law_minimal_route",
  "Core_Joint_Condition_Routes.native_joint_law.joint_law_route",
  "Core_Joint_Condition_Routes.native_joint_law.selected_joint_law_exact",
  "Core_Joint_Condition_Routes.packet_evaluation.object_discernibility_route",
  "Core_Joint_Condition_Routes.packet_evaluation.record_resolution_route"
]\<close>
end
