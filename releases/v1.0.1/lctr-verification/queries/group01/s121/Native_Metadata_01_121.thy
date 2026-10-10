theory Native_Metadata_01_121
imports
  "LCTR_Core_Rank_Reachability.Core_Rank_Reachability"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Rank_Reachability.path_increases",
  "Core_Rank_Reachability.rank_acyclic",
  "Core_Rank_Reachability.rank_partial_order"
]\<close>
end
