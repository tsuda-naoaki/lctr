theory Native_Metadata_01_037
imports
  "LCTR_Core_Differential_Selected.Core_Differential_Failure"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Differential_Failure.all_conditions_complete",
  "Core_Differential_Failure.ancestor_conjunctions_all",
  "Core_Differential_Failure.ancestor_irreflexive",
  "Core_Differential_Failure.ancestor_transitive",
  "Core_Differential_Failure.ancestors_exact",
  "Core_Differential_Failure.condition_failure_witness",
  "Core_Differential_Failure.edge_ancestor",
  "Core_Differential_Failure.jet_does_not_require_atlas",
  "Core_Differential_Failure.selected_differential.ancestor_restricts",
  "Core_Differential_Failure.selected_differential.failure_cover",
  "Core_Differential_Failure.selected_differential.failure_region_union",
  "Core_Differential_Failure.selected_differential.failure_vs_operative",
  "Core_Differential_Failure.selected_differential.finite_nonempty_failure_set",
  "Core_Differential_Failure.selected_differential.minimal_antichain",
  "Core_Differential_Failure.selected_differential.minimal_failure_witness",
  "Core_Differential_Failure.selected_differential.outside_selection_no_failure",
  "Core_Differential_Failure.selected_differential.selected_restricts",
  "Core_Differential_Failure.selected_differential.signature_nonzero",
  "Core_Differential_Failure.selected_differential.signature_support"
]\<close>
end
