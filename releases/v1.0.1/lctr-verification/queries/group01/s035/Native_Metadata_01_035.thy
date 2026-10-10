theory Native_Metadata_01_035
imports
  "LCTR_Core_Differential_Output.Core_Differential_Output"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Differential_Output.matching_differential.children_and_remainder",
  "Core_Differential_Output.matching_differential.output_parent_cover",
  "Core_Differential_Output.matching_differential.output_signature_nonzero",
  "Core_Differential_Output.matching_differential.output_unique",
  "Core_Differential_Output.matching_differential.parent_indices_antichain",
  "Core_Differential_Output.matching_differential.parent_signature_correspondence",
  "Core_Differential_Output.matching_differential.remainder_subset_parent"
]\<close>
end
