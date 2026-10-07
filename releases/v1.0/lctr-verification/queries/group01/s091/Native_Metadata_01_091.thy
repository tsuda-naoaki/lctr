theory Native_Metadata_01_091
imports
  "LCTR_Core_Local_Loop_Specification.Core_Local_Loop_Specification"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Local_Loop_Specification.directed_step",
  "Core_Local_Loop_Specification.display_injective",
  "Core_Local_Loop_Specification.domain_replacement_retains_word",
  "Core_Local_Loop_Specification.empty_domain_allowed",
  "Core_Local_Loop_Specification.separate_lists_reconstruction",
  "Core_Local_Loop_Specification.specification_shape",
  "Core_Local_Loop_Specification.tagged_domain_exact",
  "Core_Local_Loop_Specification.tuple_reconstruction",
  "Core_Local_Loop_Specification.zero_length_excluded"
]\<close>
end
