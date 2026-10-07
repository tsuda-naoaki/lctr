theory Native_Metadata_01_111
imports
  "LCTR_Core_Observer_Time.Core_Observer_Time"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Observer_Time.observer_linear.inc_equivalence",
  "Core_Observer_Time.observer_linear.order_quotient_strict_linear",
  "Core_Observer_Time.observer_linear.projection_contract",
  "Core_Observer_Time.observer_linear.strict_invariance",
  "Core_Observer_Time.observer_real.embedding_injective",
  "Core_Observer_Time.observer_real.image_inverse_contract",
  "Core_Observer_Time.observer_real.real_representation_contract",
  "Core_Observer_Time.observer_real.source_time_representation_contract",
  "Core_Observer_Time.observer_time.generated_partial",
  "Core_Observer_Time.observer_time.inc_reflexive_symmetric",
  "Core_Observer_Time.observer_time.strict_partial"
]\<close>
end
