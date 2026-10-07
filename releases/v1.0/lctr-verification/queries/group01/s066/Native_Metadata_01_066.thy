theory Native_Metadata_01_066
imports
  "LCTR_Core_Indexed_Native_Deletion.Core_Indexed_Native_Deletion"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Indexed_Native_Deletion.native_comparison.indexed_action_extension",
  "Core_Indexed_Native_Deletion.native_comparison.indexed_exact_on_old_domain",
  "Core_Indexed_Native_Deletion.native_comparison.irreducible_iff_no_indexed",
  "Core_Indexed_Native_Deletion.native_comparison.native_delete_iff",
  "Core_Indexed_Native_Deletion.native_comparison.view_injective",
  "Core_Indexed_Native_Deletion.native_comparison.view_reconstruction",
  "Core_Indexed_Native_Deletion.native_comparison.view_valid",
  "Core_Indexed_Native_Deletion.view_append",
  "Core_Indexed_Native_Deletion.view_length",
  "Core_Indexed_Native_Deletion.view_source"
]\<close>
end
