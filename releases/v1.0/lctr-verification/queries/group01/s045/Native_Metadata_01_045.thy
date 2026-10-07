theory Native_Metadata_01_045
imports
  "LCTR_Core_Dynamics_Stage_Interface.Core_Dynamics_Stage_Interface"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Stage_Interface.all_conditions",
  "Core_Dynamics_Stage_Interface.canonical_bundle",
  "Core_Dynamics_Stage_Interface.condition_failure",
  "Core_Dynamics_Stage_Interface.failure_exact",
  "Core_Dynamics_Stage_Interface.index_assignment",
  "Core_Dynamics_Stage_Interface.law_bundle",
  "Core_Dynamics_Stage_Interface.outside_exact_unformed",
  "Core_Dynamics_Stage_Interface.readiness_exact"
]\<close>
end
