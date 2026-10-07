theory Native_Metadata_01_114
imports
  "LCTR_Core_Pair_Input_Bridge.Core_Pair_Input_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Pair_Input_Bridge.empty_source_image_excludes_joint",
  "Core_Pair_Input_Bridge.empty_target_image_excludes_joint",
  "Core_Pair_Input_Bridge.joint_input_roundtrip",
  "Core_Pair_Input_Bridge.joint_input_typed",
  "Core_Pair_Input_Bridge.missing_carrier_control",
  "Core_Pair_Input_Bridge.native_joint_carrier",
  "Core_Pair_Input_Bridge.restriction_exact",
  "Core_Pair_Input_Bridge.restriction_identity_iff"
]\<close>
end
