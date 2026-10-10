theory Native_Metadata_01_049
imports
  "LCTR_Core_Evaluation_Alignment.Core_Evaluation_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Evaluation_Alignment.case_exact",
  "Core_Evaluation_Alignment.coherent_section_edge",
  "Core_Evaluation_Alignment.coherent_section_recursion",
  "Core_Evaluation_Alignment.failed_antichain",
  "Core_Evaluation_Alignment.failed_minimal",
  "Core_Evaluation_Alignment.failed_partition",
  "Core_Evaluation_Alignment.failed_requires_native_domain",
  "Core_Evaluation_Alignment.failed_set_finite",
  "Core_Evaluation_Alignment.fibres_cover",
  "Core_Evaluation_Alignment.fibres_disjoint",
  "Core_Evaluation_Alignment.path_nonsat_unformed",
  "Core_Evaluation_Alignment.state_failed_iff",
  "Core_Evaluation_Alignment.state_sat_iff",
  "Core_Evaluation_Alignment.typed_argument_unique",
  "Core_Evaluation_Alignment.update_failed_iff"
]\<close>
end
