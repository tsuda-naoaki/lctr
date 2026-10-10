theory Native_Metadata_01_118
imports
  "LCTR_Core_Partial_Sequences.Core_Partial_Sequences"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Partial_Sequences.all_partial_graphs.empty_sequence",
  "Core_Partial_Sequences.all_partial_graphs.sequence_append",
  "Core_Partial_Sequences.all_partial_graphs.sequence_append_domain",
  "Core_Partial_Sequences.all_partial_graphs.sequence_inverse_identity",
  "Core_Partial_Sequences.all_partial_graphs.sequence_partial_injectivity",
  "Core_Partial_Sequences.all_partial_graphs.sequence_reverse",
  "Core_Partial_Sequences.composition_domain",
  "Core_Partial_Sequences.empty_carrier_supported",
  "Core_Partial_Sequences.inverse_composition_on_domain",
  "Core_Partial_Sequences.partial_graph_domain",
  "Core_Partial_Sequences.partial_graph_value",
  "Core_Partial_Sequences.reverse_domain_is_image",
  "Core_Partial_Sequences.source_family.source_partial_graph",
  "Core_Partial_Sequences.source_family.source_reverse",
  "Core_Partial_Sequences.source_family.source_term_composition_identity",
  "Core_Partial_Sequences.source_family.source_term_domain",
  "Core_Partial_Sequences.source_family.source_term_inverse",
  "Core_Partial_Sequences.tagged_graph_reverse"
]\<close>
end
