theory Native_Metadata_01_159
imports
  "LCTR_Factorization_Alignment.Factorization_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Factorization_Alignment.alignment_canonical_observable_time_factorization_adapter",
  "Factorization_Alignment.alignment_canonical_observable_time_factorization_paper_wrapper",
  "Factorization_Alignment.alignment_empty_canonical_carrier_supported",
  "Factorization_Alignment.alignment_no_factor_without_equality_kernel",
  "Factorization_Alignment.alignment_no_left_inverse_without_embedding_injectivity",
  "Factorization_Alignment.alignment_quotient_trichotomy_from_order_embedding_bridge",
  "Factorization_Alignment.alignment_realImageInverse_left",
  "Factorization_Alignment.alignment_realImageInverse_right",
  "Factorization_Alignment.alignment_restrictedEmbedding_surjective",
  "Factorization_Alignment.alignment_restrictedProjection_surjective",
  "Factorization_Alignment.alignment_rho_injective_from_ordEmbSet",
  "Factorization_Alignment.alignment_scalar_time_trajectory_factorization_adapter",
  "Factorization_Alignment.alignment_selectedOrderTrajectory_factorization",
  "Factorization_Alignment.alignment_selectedOrderTrajectory_unique"
]\<close>
end
