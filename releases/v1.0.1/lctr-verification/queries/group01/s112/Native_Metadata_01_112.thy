theory Native_Metadata_01_112
imports
  "LCTR_Core_Operational_Configuration.Core_Operational_Configuration"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Operational_Configuration.body_recovery_preserves_abstraction_source",
  "Core_Operational_Configuration.detector_order_exact",
  "Core_Operational_Configuration.equal_display_retains_source_incomparability",
  "Core_Operational_Configuration.pairing_preserves_components",
  "Core_Operational_Configuration.pairing_roundtrip",
  "Core_Operational_Configuration.receiver_is_realized",
  "Core_Operational_Configuration.record_cell_partition_retained",
  "Core_Operational_Configuration.recovery_preserves_arrival",
  "Core_Operational_Configuration.recovery_returns_original",
  "Core_Operational_Configuration.role_positions_preserved",
  "Core_Operational_Configuration.source_comparison_relation_preserved",
  "Core_Operational_Configuration.source_orders_preserved"
]\<close>
end
