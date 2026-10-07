theory Native_Metadata_01_171
imports
  "LCTR_Order_Embedding_Alignment.Order_Embedding_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Order_Embedding_Alignment.alignment_brokenStrict_incomparability_not_transitive",
  "Order_Embedding_Alignment.alignment_brokenStrict_irreflexive",
  "Order_Embedding_Alignment.alignment_brokenStrict_transitive",
  "Order_Embedding_Alignment.alignment_proj_eq_iff_inc",
  "Order_Embedding_Alignment.alignment_proj_surjective",
  "Order_Embedding_Alignment.alignment_quotientLt_proj_iff",
  "Order_Embedding_Alignment.alignment_quotient_strict_linear_components",
  "Order_Embedding_Alignment.alignment_real_embedding_image_inverse_characterization",
  "Order_Embedding_Alignment.alignment_real_embedding_image_inverse_compositions",
  "Order_Embedding_Alignment.alignment_real_order_iff_map_injective"
]\<close>
end
