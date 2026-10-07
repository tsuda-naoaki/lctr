theory Native_Metadata_01_004
imports
  "LCTR_Core_Affine_Realization.Core_Affine_Realization"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Affine_Realization.affine_realization.action_free",
  "Core_Affine_Realization.affine_realization.action_transitive",
  "Core_Affine_Realization.affine_realization.coordinate_difference_sign",
  "Core_Affine_Realization.affine_realization.difference_cocycle",
  "Core_Affine_Realization.affine_realization.difference_reflexive",
  "Core_Affine_Realization.affine_realization.difference_reverse",
  "Core_Affine_Realization.affine_realization.difference_zero_iff",
  "Core_Affine_Realization.affine_realization.induced_strict_linear",
  "Core_Affine_Realization.order_embedding_pullback_iff"
]\<close>
end
