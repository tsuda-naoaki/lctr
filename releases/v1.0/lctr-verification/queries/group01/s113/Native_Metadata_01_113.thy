theory Native_Metadata_01_113
imports
  "LCTR_Core_Order_Atlas.Core_Order_Atlas"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Order_Atlas.order_domain.composite_chart_contract",
  "Core_Order_Atlas.order_domain.native_order_factor",
  "Core_Order_Atlas.order_domain.projection_kernel",
  "Core_Order_Atlas.order_domain.projection_onto",
  "Core_Order_Atlas.order_domain.projection_order",
  "Core_Order_Atlas.order_domain.quotient_strict_linear",
  "Core_Order_Atlas.order_pair.inclusion_commutes",
  "Core_Order_Atlas.order_pair.inclusion_injective",
  "Core_Order_Atlas.order_pair.inclusion_order",
  "Core_Order_Atlas.order_pair.inclusion_unique",
  "Core_Order_Atlas.order_pair.inverse_change_commutes",
  "Core_Order_Atlas.order_pair.overlap_change_commutes",
  "Core_Order_Atlas.order_pair.overlap_kernel",
  "Core_Order_Atlas.order_pair.overlap_order",
  "Core_Order_Atlas.order_triple.continue_overlap_exact",
  "Core_Order_Atlas.order_triple.inclusion_compose",
  "Core_Order_Atlas.order_triple.triple_overlap_cocycle",
  "Core_Order_Atlas.self_change_identity"
]\<close>
end
