theory Native_Metadata_01_151
imports
  "LCTR_Core_Token_Graph_Alignment.Core_Token_Graph_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Token_Graph_Alignment.acyclic",
  "Core_Token_Graph_Alignment.concrete_argument_unique",
  "Core_Token_Graph_Alignment.condition_classification_bijective",
  "Core_Token_Graph_Alignment.designated_count",
  "Core_Token_Graph_Alignment.edge_count",
  "Core_Token_Graph_Alignment.edge_lex_increasing",
  "Core_Token_Graph_Alignment.parallel_branches",
  "Core_Token_Graph_Alignment.rank_reachability_antisymm",
  "Core_Token_Graph_Alignment.reachPartialOrder",
  "Core_Token_Graph_Alignment.series_card",
  "Core_Token_Graph_Alignment.series_partition",
  "Core_Token_Graph_Alignment.source_rank_bridge",
  "Core_Token_Graph_Alignment.strict_approx_card",
  "Core_Token_Graph_Alignment.strict_approx_partition",
  "Core_Token_Graph_Alignment.token_card"
]\<close>
end
