theory Native_Metadata_01_014
imports
  "LCTR_Core_Comparison_Interfaces.Core_Comparison_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Interfaces.common_evaluation",
  "Core_Comparison_Interfaces.established_step",
  "Core_Comparison_Interfaces.evaluation_dispatch",
  "Core_Comparison_Interfaces.first_argument",
  "Core_Comparison_Interfaces.first_preceding",
  "Core_Comparison_Interfaces.index_one_unique",
  "Core_Comparison_Interfaces.index_two_unique",
  "Core_Comparison_Interfaces.later_argument",
  "Core_Comparison_Interfaces.preceding_successor",
  "Core_Comparison_Interfaces.seven_conditions"
]\<close>
end
