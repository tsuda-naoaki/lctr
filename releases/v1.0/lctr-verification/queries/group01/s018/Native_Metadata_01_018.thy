theory Native_Metadata_01_018
imports
  "LCTR_Core_Configuration_Dynamics.Core_Configuration_Dynamics"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Configuration_Dynamics.configuration_dynamics.exact_descent_pullback",
  "Core_Configuration_Dynamics.configuration_dynamics.generated_endpoint_arrived",
  "Core_Configuration_Dynamics.configuration_dynamics.generated_is_local_binding_image",
  "Core_Configuration_Dynamics.configuration_dynamics.receive_recover",
  "Core_Configuration_Dynamics.configuration_dynamics.received_body_source_position",
  "Core_Configuration_Dynamics.configuration_dynamics.recover_receive",
  "Core_Configuration_Dynamics.configuration_dynamics.recovered_source_injective",
  "Core_Configuration_Dynamics.configuration_dynamics.source_binding_pullback",
  "Core_Configuration_Dynamics.configuration_dynamics.source_binding_typed"
]\<close>
end
