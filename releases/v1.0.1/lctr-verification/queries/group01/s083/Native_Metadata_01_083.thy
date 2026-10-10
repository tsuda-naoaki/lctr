theory Native_Metadata_01_083
imports
  "LCTR_Core_Law_Refinement.Core_Law_Refinement"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Refinement.law_refinement.child_subset_parent",
  "Core_Law_Refinement.law_refinement.children_pairwise_disjoint",
  "Core_Law_Refinement.law_refinement.covered_membership",
  "Core_Law_Refinement.law_refinement.first_level_terminal",
  "Core_Law_Refinement.law_refinement.node5_covered_all",
  "Core_Law_Refinement.law_refinement.node5_unrefined_empty",
  "Core_Law_Refinement.law_refinement.parent_subset_evaluation",
  "Core_Law_Refinement.law_refinement.parent_to_native",
  "Core_Law_Refinement.law_refinement.root_decomposition",
  "Core_Law_Refinement.law_refinement.root_snapshot_monotonicity",
  "Core_Law_Refinement.law_refinement.root_unrefined_subset",
  "Core_Law_Refinement.law_refinement.unrefined_exact",
  "Core_Law_Refinement.native_remainder_formula",
  "Core_Law_Refinement.pure_cases_exclusive",
  "Core_Law_Refinement.pure_cover_formula"
]\<close>
end
