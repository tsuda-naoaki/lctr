theory Native_Metadata_09_001
imports
  "LCTR_Core_Communication_Data_Interfaces.Core_Communication_Data_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Communication_Data_Interfaces.absent_word_allowed",
  "Core_Communication_Data_Interfaces.closed_exact",
  "Core_Communication_Data_Interfaces.context_exact",
  "Core_Communication_Data_Interfaces.distributed_exact",
  "Core_Communication_Data_Interfaces.edge_kind_exhaustive",
  "Core_Communication_Data_Interfaces.empty_edges_no_links",
  "Core_Communication_Data_Interfaces.finite_graph",
  "Core_Communication_Data_Interfaces.linked_exact",
  "Core_Communication_Data_Interfaces.linked_symmetric",
  "Core_Communication_Data_Interfaces.linked_vertices",
  "Core_Communication_Data_Interfaces.metric_intervals",
  "Core_Communication_Data_Interfaces.one_way_is_sufficient",
  "Core_Communication_Data_Interfaces.probability_bounds",
  "Core_Communication_Data_Interfaces.single_edge_links",
  "Core_Communication_Data_Interfaces.walk_adjacent",
  "Core_Communication_Data_Interfaces.walk_endpoints",
  "Core_Communication_Data_Interfaces.walk_positive",
  "Core_Communication_Data_Interfaces.word_domain_exact",
  "Core_Communication_Data_Interfaces.word_single_valued"
]\<close>
end
