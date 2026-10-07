theory Native_Metadata_01_131
imports
  "LCTR_Core_Relative_Class_Witness.Core_Relative_Class_Witness"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Relative_Class_Witness.product_nonempty",
  "Core_Relative_Class_Witness.supplied_image",
  "Core_Relative_Class_Witness.witness_family"
]\<close>
end
