theory Native_Metadata_01_071
imports
  "LCTR_Core_Joint_Real_Image.Core_Joint_Real_Image"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Real_Image.native_joint_law.ambient_relation_image",
  "Core_Joint_Real_Image.native_joint_law.domain_image",
  "Core_Joint_Real_Image.native_joint_law.projection_inverse",
  "Core_Joint_Real_Image.native_joint_law.relation_image"
]\<close>
end
