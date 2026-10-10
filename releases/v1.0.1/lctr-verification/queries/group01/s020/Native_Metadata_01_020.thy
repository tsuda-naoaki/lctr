theory Native_Metadata_01_020
imports
  "LCTR_Core_Configuration_Order.Core_Configuration_Order"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Configuration_Order.clock_order_exact",
  "Core_Configuration_Order.configuration_order.native_partial_order",
  "Core_Configuration_Order.configuration_order.original_source_order",
  "Core_Configuration_Order.configuration_order.projection_preserved",
  "Core_Configuration_Order.configuration_order.quotient_preserved",
  "Core_Configuration_Order.configuration_ordered.native_local_global_compatible",
  "Core_Configuration_Order.configuration_ordered.native_ordered_output_unique",
  "Core_Configuration_Order.configuration_ordered.native_representation_kernel",
  "Core_Configuration_Order.configuration_ordered.native_representation_order",
  "Core_Configuration_Order.distinct_clock_sources_incomparable",
  "Core_Configuration_Order.record_order_exact"
]\<close>
end
