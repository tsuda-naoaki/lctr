theory Native_Metadata_01_030
imports
  "LCTR_Core_Continuum_Topology_Alignment.Core_Continuum_Topology_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Topology_Alignment.missing_input_control",
  "Core_Continuum_Topology_Alignment.open_neighborhood_iff",
  "Core_Continuum_Topology_Alignment.operational_robust_domain_open",
  "Core_Continuum_Topology_Alignment.positive_domain_open",
  "Core_Continuum_Topology_Alignment.robust_positive_iff",
  "Core_Continuum_Topology_Alignment.source_order_topology_neighborhood"
]\<close>
end
