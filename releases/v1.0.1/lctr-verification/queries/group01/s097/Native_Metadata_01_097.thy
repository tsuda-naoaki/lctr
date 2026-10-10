theory Native_Metadata_01_097
imports
  "LCTR_Core_Native_Joint_Relation.Core_Native_Joint_Relation"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Joint_Relation.native_joint_curves.every_trajectory_representative_agrees",
  "Core_Native_Joint_Relation.native_joint_curves.joint_relation_unique",
  "Core_Native_Joint_Relation.native_joint_curves.joint_source_membership",
  "Core_Native_Joint_Relation.native_joint_curves.native_relation_typed",
  "Core_Native_Joint_Relation.native_joint_curves.native_source_descent",
  "Core_Native_Joint_Relation.native_joint_curves.source_projection_components",
  "Core_Native_Joint_Relation.native_joint_curves.source_projection_kernel",
  "Core_Native_Joint_Relation.native_joint_curves.source_projection_surjective",
  "Core_Native_Joint_Relation.native_joint_curves.trajectory_has_source_representative"
]\<close>
end
