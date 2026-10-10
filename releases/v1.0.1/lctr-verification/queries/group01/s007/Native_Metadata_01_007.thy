theory Native_Metadata_01_007
imports
  "LCTR_Core_Burden_Comparison.Core_Burden_Comparison"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Burden_Comparison.equality_iff_empty_symmetric_difference",
  "Core_Burden_Comparison.one_sided_separation",
  "Core_Burden_Comparison.two_sided_incomparability"
]\<close>
end
