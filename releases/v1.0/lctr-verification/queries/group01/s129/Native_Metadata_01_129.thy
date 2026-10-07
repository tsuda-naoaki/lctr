theory Native_Metadata_01_129
imports
  "LCTR_Core_Refinement_Forest.Core_Refinement_Forest"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Refinement_Forest.native_comparison_forest_laws",
  "Core_Refinement_Forest.refinement_forest.ancestor_inclusion",
  "Core_Refinement_Forest.refinement_forest.child_family_with_remainder",
  "Core_Refinement_Forest.refinement_forest.covered_subset",
  "Core_Refinement_Forest.refinement_forest.node_decomposition",
  "Core_Refinement_Forest.snapshot_monotonicity",
  "Core_Refinement_Forest.two_level_regions.two_level_acyclic",
  "Core_Refinement_Forest.two_level_regions.two_level_child_depth",
  "Core_Refinement_Forest.two_level_regions.two_level_leaf"
]\<close>
end
