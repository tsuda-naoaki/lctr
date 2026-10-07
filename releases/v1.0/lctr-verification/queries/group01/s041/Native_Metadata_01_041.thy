theory Native_Metadata_01_041
imports
  "LCTR_Core_Dynamics_Execution.Core_Dynamics_Execution"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Execution.absent_upstream_passes",
  "Core_Dynamics_Execution.final_pair_failure",
  "Core_Dynamics_Execution.four_root_failures_and_descendants",
  "Core_Dynamics_Execution.missing_formation_blocks_descendant",
  "Core_Dynamics_Execution.missing_formation_not_failure",
  "Core_Dynamics_Execution.root_failure",
  "Core_Dynamics_Execution.test_input_sat",
  "Core_Dynamics_Execution.upstream_passes"
]\<close>
end
