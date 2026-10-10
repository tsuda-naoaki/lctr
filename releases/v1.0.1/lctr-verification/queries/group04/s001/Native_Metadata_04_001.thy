theory Native_Metadata_04_001
imports
  "LCTR_Core_Abstract_Word_Encoding.Core_Abstract_Word_Encoding"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Abstract_Word_Encoding.decode_encode",
  "Core_Abstract_Word_Encoding.tuple_lengths",
  "Core_Abstract_Word_Encoding.typed_kind_actions.action_preservation",
  "Core_Abstract_Word_Encoding.typed_kind_actions.append_display",
  "Core_Abstract_Word_Encoding.typed_kind_actions.append_encoding",
  "Core_Abstract_Word_Encoding.typed_kind_actions.displayed_tuple_injective",
  "Core_Abstract_Word_Encoding.typed_kind_actions.encode_decode",
  "Core_Abstract_Word_Encoding.typed_kind_actions.encoding_bijective",
  "Core_Abstract_Word_Encoding.typed_kind_actions.reverse_encoding",
  "Core_Abstract_Word_Encoding.typed_kind_actions.tuple_reconstruction"
]\<close>
end
