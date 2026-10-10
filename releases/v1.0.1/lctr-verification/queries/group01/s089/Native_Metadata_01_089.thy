theory Native_Metadata_01_089
imports
  "LCTR_Core_Local_Loop_Bridge.Core_Local_Loop_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Local_Loop_Bridge.decode_encode",
  "Core_Local_Loop_Bridge.encoded_pure",
  "Core_Local_Loop_Bridge.encoding_injective",
  "Core_Local_Loop_Bridge.length_preserved",
  "Core_Local_Loop_Bridge.native_comparison.candidate_partial_injection",
  "Core_Local_Loop_Bridge.native_comparison.encode_decode",
  "Core_Local_Loop_Bridge.native_comparison.native_spec_fields",
  "Core_Local_Loop_Bridge.native_comparison.native_spec_positive"
]\<close>
end
