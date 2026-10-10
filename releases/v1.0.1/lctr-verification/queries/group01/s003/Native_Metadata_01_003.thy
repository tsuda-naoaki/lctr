theory Native_Metadata_01_003
imports
  "LCTR_Core_Affine_Order_Bridge.Core_Affine_Order_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Affine_Order_Bridge.affine_realization.difference_nonnegative_closure"
]\<close>
end
