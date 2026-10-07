theory Native_Metadata_01_046
imports
  "LCTR_Core_Dynamics_Tokens.Core_Dynamics_Tokens"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Tokens.condition_correspondence",
  "Core_Dynamics_Tokens.failed_intersection_image",
  "Core_Dynamics_Tokens.failure_iff_minimal",
  "Core_Dynamics_Tokens.false_condition_has_failure",
  "Core_Dynamics_Tokens.incoming_edges_exact",
  "Core_Dynamics_Tokens.minimal_false_iff",
  "Core_Dynamics_Tokens.minimal_set_nonempty",
  "Core_Dynamics_Tokens.ready_iff_ancestor_conditions",
  "Core_Dynamics_Tokens.recursive_failure",
  "Core_Dynamics_Tokens.sat_implies_condition",
  "Core_Dynamics_Tokens.simultaneous_minima",
  "Core_Dynamics_Tokens.stage_failure_iff",
  "Core_Dynamics_Tokens.stage_intersection_nonempty",
  "Core_Dynamics_Tokens.token_bijection",
  "Core_Dynamics_Tokens.unconditional_antichain",
  "Core_Dynamics_Tokens.upstream_failure_blocks_all",
  "Core_Dynamics_Tokens.within_edges_exact"
]\<close>
end
