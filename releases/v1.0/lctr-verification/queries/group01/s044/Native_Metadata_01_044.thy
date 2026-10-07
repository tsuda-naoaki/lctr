theory Native_Metadata_01_044
imports
  "LCTR_Core_Dynamics_Recovery_Data.Core_Dynamics_Recovery_Data"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Recovery_Data.generated_endpoint_arrived",
  "Core_Dynamics_Recovery_Data.generated_exact",
  "Core_Dynamics_Recovery_Data.local_binding_exact",
  "Core_Dynamics_Recovery_Data.package_components",
  "Core_Dynamics_Recovery_Data.recovery_domain",
  "Core_Dynamics_Recovery_Data.recovery_exists",
  "Core_Dynamics_Recovery_Data.recovery_injective",
  "Core_Dynamics_Recovery_Data.recovery_right_inverse",
  "Core_Dynamics_Recovery_Data.right_inverse_not_injectivity",
  "Core_Dynamics_Recovery_Data.source_binding_exact",
  "Core_Dynamics_Recovery_Data.source_binding_pullback",
  "Core_Dynamics_Recovery_Data.source_binding_typed"
]\<close>
end
