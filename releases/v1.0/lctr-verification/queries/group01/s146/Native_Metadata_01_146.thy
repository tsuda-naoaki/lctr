theory Native_Metadata_01_146
imports
  "LCTR_Core_Stage_Boundaries.Core_Stage_Boundaries"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Stage_Boundaries.stage_boundaries.differential_failure_boundary",
  "Core_Stage_Boundaries.stage_boundaries.differential_failure_outside_domain",
  "Core_Stage_Boundaries.stage_boundaries.differential_requires_same_law",
  "Core_Stage_Boundaries.stage_boundaries.dynamics_failure_not_operative",
  "Core_Stage_Boundaries.stage_boundaries.dynamics_law_failures_disjoint",
  "Core_Stage_Boundaries.stage_boundaries.law_differential_failures_disjoint",
  "Core_Stage_Boundaries.stage_boundaries.law_failure_not_operative",
  "Core_Stage_Boundaries.stage_boundaries.law_failure_requires_dynamics"
]\<close>
end
