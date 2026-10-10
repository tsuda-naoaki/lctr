theory Native_Metadata_01_070
imports
  "LCTR_Core_Joint_Law_Evaluation.Core_Joint_Law_Evaluation"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Law_Evaluation.native_joint_law.common_valid_joint_tuples",
  "Core_Joint_Law_Evaluation.native_joint_law.five_condition_connection",
  "Core_Joint_Law_Evaluation.native_joint_law.individual_observable_component",
  "Core_Joint_Law_Evaluation.native_joint_law.inverse_on_projection",
  "Core_Joint_Law_Evaluation.native_joint_law.joint_failure_exact",
  "Core_Joint_Law_Evaluation.native_joint_law.joint_minimal_failure_cover",
  "Core_Joint_Law_Evaluation.native_joint_law.joint_relation_component_valid",
  "Core_Joint_Law_Evaluation.native_joint_law.joint_relation_source_valid",
  "Core_Joint_Law_Evaluation.native_joint_law.real_projection_bijective",
  "Core_Joint_Law_Evaluation.native_joint_law.real_value_injective",
  "Core_Joint_Law_Evaluation.native_joint_law.tuple_components"
]\<close>
end
