theory Native_Metadata_01_145
imports
  "LCTR_Core_Source_Recovery.Core_Source_Recovery"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Source_Recovery.b_recovery_preserves_object_position",
  "Core_Source_Recovery.c_distinct_sources_incomparable",
  "Core_Source_Recovery.c_family_partial_order",
  "Core_Source_Recovery.c_recovery_preserves_source_index",
  "Core_Source_Recovery.c_within_source_partial_order",
  "Core_Source_Recovery.d_equal_index_incomparable",
  "Core_Source_Recovery.d_partial_order",
  "Core_Source_Recovery.empty_arrival_has_no_recoverable_value",
  "Core_Source_Recovery.equal_display_does_not_identify_tokens",
  "Core_Source_Recovery.fiber_eq_singleton_recovery",
  "Core_Source_Recovery.fixed_source_order_correspondence",
  "Core_Source_Recovery.missing_class_condition_allows_overlap",
  "Core_Source_Recovery.positive_c_distinct_sources_same_nat",
  "Core_Source_Recovery.positive_constant_display_preserves_token_identity",
  "Core_Source_Recovery.positive_d_distinct_tokens_same_seq",
  "Core_Source_Recovery.positive_d_equal_seq_incomparable",
  "Core_Source_Recovery.positive_empty_arrival_domain_allowed",
  "Core_Source_Recovery.record_cells_partition_criterion",
  "Core_Source_Recovery.singleton_fiber_recovery",
  "Core_Source_Recovery.two_source_one_arrival_not_uniquely_recoverable",
  "Core_Source_Recovery.unique_tagged_representation"
]\<close>
end
