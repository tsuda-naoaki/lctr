theory Native_Metadata_01_054
imports
  "LCTR_Core_Failure_Multiplicity.Core_Failure_Multiplicity"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Failure_Multiplicity.absent_exact",
  "Core_Failure_Multiplicity.classification_exact",
  "Core_Failure_Multiplicity.classified_nonzero_has_boundary",
  "Core_Failure_Multiplicity.multiplicity_components",
  "Core_Failure_Multiplicity.multiplicity_depends_on_two_cardinalities",
  "Core_Failure_Multiplicity.no_boundary_no_support",
  "Core_Failure_Multiplicity.parallel_boundary_card",
  "Core_Failure_Multiplicity.parallel_exact",
  "Core_Failure_Multiplicity.parallel_structural_card",
  "Core_Failure_Multiplicity.present_zero_boundary_is_absent",
  "Core_Failure_Multiplicity.quantitative_parallel_at_boundary",
  "Core_Failure_Multiplicity.quantitative_signature_support",
  "Core_Failure_Multiplicity.support_at_boundary",
  "Core_Failure_Multiplicity.support_card_bound",
  "Core_Failure_Multiplicity.unique_exact"
]\<close>
end
