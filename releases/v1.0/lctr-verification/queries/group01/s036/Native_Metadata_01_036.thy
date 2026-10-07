theory Native_Metadata_01_036
imports
  "LCTR_Core_Differential_Refinement.Core_Differential_Refinement"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Differential_Refinement.differential_refinement.all_node_decompositions",
  "Core_Differential_Refinement.differential_refinement.ancestor_region_inclusion",
  "Core_Differential_Refinement.differential_refinement.child_and_remainder_typing",
  "Core_Differential_Refinement.differential_refinement.conditional_disjoint_children",
  "Core_Differential_Refinement.differential_refinement.first_split_exact",
  "Core_Differential_Refinement.differential_refinement.root_snapshot_monotonicity",
  "Core_Differential_Refinement.differential_refinement.root_split_exact",
  "Core_Differential_Refinement.differential_refinement.second_level_terminal",
  "Core_Differential_Refinement.matching_differential.parent_requires_selection",
  "Core_Differential_Refinement.matching_differential.parent_source_exact",
  "Core_Differential_Refinement.matching_differential.parent_subset_evaluation",
  "Core_Differential_Refinement.matching_differential.parents_cover"
]\<close>
end
