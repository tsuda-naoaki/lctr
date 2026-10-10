theory Native_Metadata_01_142
imports
  "LCTR_Core_Selected_Generated_Law.Core_Selected_Generated_Law"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Selected_Generated_Law.generated_common_representability",
  "Core_Selected_Generated_Law.generated_exact",
  "Core_Selected_Generated_Law.generated_selection.forget_retains_specification",
  "Core_Selected_Generated_Law.generated_selection.outside_selection_not_failure",
  "Core_Selected_Generated_Law.generated_selection.selected_condition_exact",
  "Core_Selected_Generated_Law.generated_selection.selected_domain_ready",
  "Core_Selected_Generated_Law.generated_selection.selected_failure_operative",
  "Core_Selected_Generated_Law.generated_selection.selected_generation_components",
  "Core_Selected_Generated_Law.generated_selection.selected_time_admissibility",
  "Core_Selected_Generated_Law.proper_generated_subdomain_possible"
]\<close>
end
