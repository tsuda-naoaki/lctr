theory Native_Metadata_01_080
imports
  "LCTR_Core_Law_Failure.Core_Law_Failure"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Failure.ancestors_exact",
  "Core_Law_Failure.edge_rank",
  "Core_Law_Failure.graph_acyclic"
]\<close>
end
