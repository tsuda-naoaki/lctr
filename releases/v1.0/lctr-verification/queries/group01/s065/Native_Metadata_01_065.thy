theory Native_Metadata_01_065
imports
  "LCTR_Core_Indexed_Deletion.Core_Indexed_Deletion"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Indexed_Deletion.cut_decomposition",
  "Core_Indexed_Deletion.cut_lengths",
  "Core_Indexed_Deletion.deletion_preserves_typing",
  "Core_Indexed_Deletion.erased_display",
  "Core_Indexed_Deletion.indexed_iff_segment",
  "Core_Indexed_Deletion.no_deletion_equivalence",
  "Core_Indexed_Deletion.node_display",
  "Core_Indexed_Deletion.slice_source_iff",
  "Core_Indexed_Deletion.terminal_append",
  "Core_Indexed_Deletion.valid_append"
]\<close>
end
