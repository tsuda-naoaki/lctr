theory Native_Metadata_01_172
imports
  "LCTR_Region_Law_Alignment.Region_Law_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Region_Law_Alignment.actual_law_component.alignment_candRelDom_is_exact_relation_domain",
  "Region_Law_Alignment.actual_law_component.alignment_empty_relation_has_empty_domain",
  "Region_Law_Alignment.actual_law_component.alignment_evalPoint_is_in_actual_evalDom",
  "Region_Law_Alignment.actual_law_component.alignment_graph_set_equality_of_pointwise",
  "Region_Law_Alignment.actual_law_component.alignment_law_candidate_relation_literal_graph",
  "Region_Law_Alignment.actual_law_component.alignment_law_candidate_relation_partial_output_map",
  "Region_Law_Alignment.actual_law_component.alignment_no_graph_if_right_uniqueness_fails",
  "Region_Law_Alignment.alignment_canonical_output_not_generated",
  "Region_Law_Alignment.alignment_closure_subset_safeSet",
  "Region_Law_Alignment.alignment_dep_rule_iff",
  "Region_Law_Alignment.alignment_genDef_is_least_closure_membership",
  "Region_Law_Alignment.alignment_global_gluing_failure_blocks_representation_entry",
  "Region_Law_Alignment.alignment_operative_failure_from_definition",
  "Region_Law_Alignment.alignment_req_contains_operative",
  "Region_Law_Alignment.alignment_safeSet_closed",
  "Region_Law_Alignment.alignment_supplied_output_remains_generated"
]\<close>
end
