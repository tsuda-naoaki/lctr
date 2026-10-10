theory Native_Metadata_01_099
imports
  "LCTR_Core_Native_Law_Failure.Core_Native_Law_Failure"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Law_Failure.native_law_context.native_failure_exact",
  "Core_Native_Law_Failure.selected_law_family.ancestors_explicit",
  "Core_Native_Law_Failure.selected_law_family.failure_covered_by_minimal_classes",
  "Core_Native_Law_Failure.selected_law_family.failure_domain_union",
  "Core_Native_Law_Failure.selected_law_family.failure_on_selected_datum",
  "Core_Native_Law_Failure.selected_law_family.finite_witness_set",
  "Core_Native_Law_Failure.selected_law_family.minimal_classes_antichain",
  "Core_Native_Law_Failure.selected_law_family.outside_selection_not_failure",
  "Core_Native_Law_Failure.selected_law_family.selected_condition_exact"
]\<close>
end
