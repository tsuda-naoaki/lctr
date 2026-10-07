theory Native_Metadata_01_082
imports
  "LCTR_Core_Law_Readiness.Core_Law_Readiness"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Readiness.proper_subdomain_permitted",
  "Core_Law_Readiness.ready_selection.failure_vs_operative",
  "Core_Law_Readiness.ready_selection.law_failure_requires_dynamics",
  "Core_Law_Readiness.ready_selection.law_operative_on_selected_datum",
  "Core_Law_Readiness.ready_selection.no_failure_outside_selected_domain",
  "Core_Law_Readiness.ready_selection.selected_datum_ready",
  "Core_Law_Readiness.single_ready_exact"
]\<close>
end
