theory Native_Metadata_01_107
imports
  "LCTR_Core_Native_Word_Families.Core_Native_Word_Families"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Word_Families.append_counts",
  "Core_Native_Word_Families.common_pure_family_iff_empty",
  "Core_Native_Word_Families.four_cases_exist_unique",
  "Core_Native_Word_Families.length_partition",
  "Core_Native_Word_Families.native_comparison.extended_action_laws",
  "Core_Native_Word_Families.native_comparison.native_partial_injectivity",
  "Core_Native_Word_Families.native_comparison.source_action_laws",
  "Core_Native_Word_Families.native_comparison.standard_embeddings_injective",
  "Core_Native_Word_Families.native_comparison.standard_embeddings_operations",
  "Core_Native_Word_Families.native_comparison.transport_action_laws",
  "Core_Native_Word_Families.native_comparison.unique_pure_preimages",
  "Core_Native_Word_Families.pure_families_closed",
  "Core_Native_Word_Families.reverse_counts",
  "Core_Native_Word_Families.source_only_iff",
  "Core_Native_Word_Families.transport_only_iff"
]\<close>
end
