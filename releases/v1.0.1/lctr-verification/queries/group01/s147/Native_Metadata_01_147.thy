theory Native_Metadata_01_147
imports
  "LCTR_Core_Strict_Partial_Order.Core_Strict_Partial_Order"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Strict_Partial_Order.strict_part_contract"
]\<close>
end
