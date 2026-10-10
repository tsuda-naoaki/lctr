theory Native_Metadata_01_062
imports
  "LCTR_Core_First_Failure_Report.Core_First_Failure_Report"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_First_Failure_Report.boundary_empty_iff",
  "Core_First_Failure_Report.boundary_empty_or_singleton",
  "Core_First_Failure_Report.boundary_presence_different_from_zero_signature",
  "Core_First_Failure_Report.boundary_singleton",
  "Core_First_Failure_Report.excess_signature_exact",
  "Core_First_Failure_Report.excess_signature_zero_iff",
  "Core_First_Failure_Report.full_validity_has_no_boundary",
  "Core_First_Failure_Report.localization_nonempty",
  "Core_First_Failure_Report.minimal_positions_exact",
  "Core_First_Failure_Report.minimal_signature_exact",
  "Core_First_Failure_Report.no_least_boundary_control",
  "Core_First_Failure_Report.parallel_structural_positions",
  "Core_First_Failure_Report.quantitative_boundary_singleton",
  "Core_First_Failure_Report.report_components",
  "Core_First_Failure_Report.report_independent_of_solution",
  "Core_First_Failure_Report.signature_support_exact",
  "Core_First_Failure_Report.unique_structural_position"
]\<close>
end
