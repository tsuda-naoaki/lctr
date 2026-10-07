theory Native_Metadata_01_019
imports
  "LCTR_Core_Configuration_Observer_Time.Core_Configuration_Observer_Time"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Configuration_Observer_Time.configuration_observer.body_generator_exact",
  "Core_Configuration_Observer_Time.configuration_observer.body_quotient_kernel",
  "Core_Configuration_Observer_Time.configuration_observer.clock_generator_exact",
  "Core_Configuration_Observer_Time.configuration_observer.clock_quotient_kernel",
  "Core_Configuration_Observer_Time.configuration_observer.observer_partial_order",
  "Core_Configuration_Observer_Time.configuration_observer.observer_source_order_step",
  "Core_Configuration_Observer_Time.configuration_observer.real_time_source_contract",
  "Core_Configuration_Observer_Time.configuration_observer.source_trajectory_exact",
  "Core_Configuration_Observer_Time.pack_roundtrip"
]\<close>
end
