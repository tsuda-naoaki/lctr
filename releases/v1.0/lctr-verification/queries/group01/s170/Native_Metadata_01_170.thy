theory Native_Metadata_01_170
imports
  "LCTR_Nested_Quotient_Order_Alignment.Nested_Quotient_Order_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Nested_Quotient_Order_Alignment.nested_quotient_order_embedding"
]\<close>
end
