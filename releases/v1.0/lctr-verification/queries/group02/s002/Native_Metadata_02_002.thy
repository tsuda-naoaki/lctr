theory Native_Metadata_02_002
imports
  "LCTR_Core_Dag_Alignment.Core_Dag_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dag_Alignment.cyclic_update_can_have_multiple_solutions",
  "Core_Dag_Alignment.cyclic_update_can_have_no_solution",
  "Core_Dag_Alignment.edge_orientation_control",
  "Core_Dag_Alignment.empty_vertices_allow_empty_states",
  "Core_Dag_Alignment.finite_dag_deterministic_state_fold"
]\<close>
end
