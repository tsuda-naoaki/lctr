theory Native_Metadata_01_117
imports
  "LCTR_Core_Partial_Map_Bridge.Core_Partial_Map_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Partial_Map_Bridge.composition_functional",
  "Core_Partial_Map_Bridge.empty_domain_composition",
  "Core_Partial_Map_Bridge.general_composition_domain",
  "Core_Partial_Map_Bridge.map_graph_domain",
  "Core_Partial_Map_Bridge.map_graph_value",
  "Core_Partial_Map_Bridge.noninjective_composition_control",
  "Core_Partial_Map_Bridge.partial_map_composition"
]\<close>
end
