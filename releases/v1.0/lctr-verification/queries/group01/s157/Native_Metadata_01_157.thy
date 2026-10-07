theory Native_Metadata_01_157
imports
  "LCTR_Core_Word_Encoding.Core_Word_Encoding"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Word_Encoding.decode_encode",
  "Core_Word_Encoding.displayed_tuple_injective",
  "Core_Word_Encoding.edges_injective",
  "Core_Word_Encoding.kinds_from_edges",
  "Core_Word_Encoding.native_comparison.action_preservation",
  "Core_Word_Encoding.native_comparison.domain_preservation",
  "Core_Word_Encoding.native_comparison.encode_decode",
  "Core_Word_Encoding.native_comparison.encoding_bijective",
  "Core_Word_Encoding.native_comparison.native_display_injective",
  "Core_Word_Encoding.native_comparison.native_display_unique",
  "Core_Word_Encoding.native_length_preserved",
  "Core_Word_Encoding.positions_from_edges",
  "Core_Word_Encoding.tuple_lengths"
]\<close>
end
