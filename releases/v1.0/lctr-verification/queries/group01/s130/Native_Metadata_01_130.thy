theory Native_Metadata_01_130
imports
  "LCTR_Core_Refinement_Paths.Core_Refinement_Paths"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Refinement_Paths.arbitrary_depth_control",
  "Core_Refinement_Paths.child_closure",
  "Core_Refinement_Paths.nodes_iff",
  "Core_Refinement_Paths.path_length",
  "Core_Refinement_Paths.path_regions.acyclic",
  "Core_Refinement_Paths.path_regions.ancestor_inclusion",
  "Core_Refinement_Paths.path_regions.child_depth",
  "Core_Refinement_Paths.path_regions.child_edge_exact",
  "Core_Refinement_Paths.path_regions.empty_leaf",
  "Core_Refinement_Paths.path_regions.node_decomposition",
  "Core_Refinement_Paths.path_successor",
  "Core_Refinement_Paths.path_zero",
  "Core_Refinement_Paths.tagged_truncation_injective",
  "Core_Refinement_Paths.tagged_truncation_range",
  "Core_Refinement_Paths.truncated_exact",
  "Core_Refinement_Paths.unique_level"
]\<close>
end
