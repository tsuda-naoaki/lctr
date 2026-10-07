theory Native_Metadata_04_002
imports
  "LCTR_Core_Audit_Report.Core_Audit_Report"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Audit_Report.approximation_boundary_uses_local_reasons",
  "Core_Audit_Report.approximation_reasons_subset",
  "Core_Audit_Report.diagnostic_values_when_defined",
  "Core_Audit_Report.failed_position_uses_global_reasons",
  "Core_Audit_Report.native_failure_signature",
  "Core_Audit_Report.native_group_maximum",
  "Core_Audit_Report.native_indeterminate_signature",
  "Core_Audit_Report.native_report_matches",
  "Core_Audit_Report.native_report_unique",
  "Core_Audit_Report.report_independent_of_solution",
  "Core_Audit_Report.report_preserves_data",
  "Core_Audit_Report.union_group_reasons"
]\<close>
end
