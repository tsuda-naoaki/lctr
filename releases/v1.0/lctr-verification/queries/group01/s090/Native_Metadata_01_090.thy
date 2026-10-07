theory Native_Metadata_01_090
imports
  "LCTR_Core_Local_Loop_Realization.Core_Local_Loop_Realization"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Local_Loop_Realization.control_global_identity_fails",
  "Core_Local_Loop_Realization.control_path_pure",
  "Core_Local_Loop_Realization.native_comparison.empty_specification",
  "Core_Local_Loop_Realization.native_comparison.global_identity_restricts",
  "Core_Local_Loop_Realization.native_comparison.realizable_iff_total_realization",
  "Core_Local_Loop_Realization.native_comparison.realization_correct",
  "Core_Local_Loop_Realization.native_comparison.realization_graph",
  "Core_Local_Loop_Realization.native_comparison.realization_injective",
  "Core_Local_Loop_Realization.native_comparison.realization_unique",
  "Core_Local_Loop_Realization.native_comparison.restriction_agrees",
  "Core_Local_Loop_Realization.native_comparison.restriction_realizable",
  "Core_Local_Loop_Realization.native_comparison.specified_identity_iff",
  "Core_Local_Loop_Realization.specified_identity_does_not_imply_global"
]\<close>
end
