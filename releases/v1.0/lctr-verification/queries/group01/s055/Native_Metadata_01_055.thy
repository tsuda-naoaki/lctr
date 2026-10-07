theory Native_Metadata_01_055
imports
  "LCTR_Core_Finite_Audit.Core_Finite_Audit"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Audit.audit_output_eq_native",
  "Core_Finite_Audit.count_bound",
  "Core_Finite_Audit.finite_audit_output_unique",
  "Core_Finite_Audit.finite_run_solves",
  "Core_Finite_Audit.finite_run_unique",
  "Core_Finite_Audit.lookup_tabulate",
  "Core_Finite_Audit.predecessor_iff",
  "Core_Finite_Audit.rank_bound",
  "Core_Finite_Audit.run_matches_solution",
  "Core_Finite_Audit.step_eq_native"
]\<close>
end
