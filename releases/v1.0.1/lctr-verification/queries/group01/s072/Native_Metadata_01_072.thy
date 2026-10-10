theory Native_Metadata_01_072
imports
  "LCTR_Core_Joint_Time.Core_Joint_Time"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Time.common_native_time.embedding_transfers",
  "Core_Joint_Time.common_native_time.order_map_unique",
  "Core_Joint_Time.common_native_time.order_maps_inverse",
  "Core_Joint_Time.common_native_time.order_projection_agrees",
  "Core_Joint_Time.common_native_time.order_strict_agrees",
  "Core_Joint_Time.common_native_time.time_incomparability_agrees",
  "Core_Joint_Time.common_native_time.time_maps_inverse",
  "Core_Joint_Time.common_native_time.time_order_agrees",
  "Core_Joint_Time.common_native_time.time_projection_agrees",
  "Core_Joint_Time.common_native_time.time_quotient_types_equal",
  "Core_Joint_Time.common_native_time.time_setoids_equal",
  "Core_Joint_Time.common_native_time.time_strict_agrees",
  "Core_Joint_Time.native_joint_curves.joint_relation_on_actual_states",
  "Core_Joint_Time.native_joint_curves.native_joint_components",
  "Core_Joint_Time.native_joint_curves.native_joint_unique"
]\<close>
end
