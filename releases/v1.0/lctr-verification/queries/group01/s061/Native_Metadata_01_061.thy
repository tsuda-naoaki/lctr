theory Native_Metadata_01_061
imports
  "LCTR_Core_Finite_Tuple_Data.Core_Finite_Tuple_Data"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Tuple_Data.concatenate_cons",
  "Core_Finite_Tuple_Data.concatenate_empty_left",
  "Core_Finite_Tuple_Data.concatenate_injective",
  "Core_Finite_Tuple_Data.concatenate_split",
  "Core_Finite_Tuple_Data.concatenated_length",
  "Core_Finite_Tuple_Data.seven_components",
  "Core_Finite_Tuple_Data.split_concatenate"
]\<close>
end
