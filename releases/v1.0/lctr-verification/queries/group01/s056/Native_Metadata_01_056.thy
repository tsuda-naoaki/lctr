theory Native_Metadata_01_056
imports
  "LCTR_Core_Finite_Class_Witness.Core_Finite_Class_Witness"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Class_Witness.finite_witness_set",
  "Core_Finite_Class_Witness.two_members"
]\<close>
end
