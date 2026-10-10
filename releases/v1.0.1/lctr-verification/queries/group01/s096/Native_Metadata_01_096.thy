theory Native_Metadata_01_096
imports
  "LCTR_Core_Native_Joint_Jets.Core_Native_Joint_Jets"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Joint_Jets.joint_atlas_realizations.joint_extension_agrees",
  "Core_Native_Joint_Jets.joint_atlas_realizations.joint_extension_in_region",
  "Core_Native_Joint_Jets.joint_atlas_realizations.joint_extension_smooth",
  "Core_Native_Joint_Jets.joint_atlas_realizations.joint_jet_independent_of_realizations",
  "Core_Native_Joint_Jets.joint_atlas_realizations.joint_realizations_agree_nearby",
  "Core_Native_Joint_Jets.joint_atlas_realizations.joint_zeroth_is_generated",
  "Core_Native_Joint_Jets.joint_atlas_realizations.relation_membership_exact",
  "Core_Native_Joint_Jets.native_real_component_chart.joint_jets_all_time_embeddings",
  "Core_Native_Joint_Jets.native_real_component_chart.joint_zeroth_native_values",
  "Core_Native_Joint_Jets.pushed_generated_pair",
  "Core_Native_Joint_Jets.pushed_joint_extension",
  "Core_Native_Joint_Jets.pushed_joint_jet",
  "Core_Native_Joint_Jets.real_transported_atlas.pushed_relation_membership"
]\<close>
end
