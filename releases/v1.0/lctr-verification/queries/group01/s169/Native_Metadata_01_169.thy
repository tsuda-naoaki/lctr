theory Native_Metadata_01_169
imports
  "LCTR_Native_Selected_Differential_Alignment.Native_Selected_Differential_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Native_Selected_Differential_Alignment.operative_on_domain",
  "Native_Selected_Differential_Alignment.operative_requires_same_law",
  "Native_Selected_Differential_Alignment.outside_selection_unformed",
  "Native_Selected_Differential_Alignment.selected_condition_native",
  "Native_Selected_Differential_Alignment.selected_differential_owned",
  "Native_Selected_Differential_Alignment.selected_failure_cover",
  "Native_Selected_Differential_Alignment.selected_failure_exact",
  "Native_Selected_Differential_Alignment.selected_law_owned",
  "Native_Selected_Differential_Alignment.selected_minimal_counter",
  "Native_Selected_Differential_Alignment.selected_native_synthesis(1)",
  "Native_Selected_Differential_Alignment.selected_native_synthesis(2)"
]\<close>
end
