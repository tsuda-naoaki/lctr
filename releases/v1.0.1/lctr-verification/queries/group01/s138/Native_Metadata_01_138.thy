theory Native_Metadata_01_138
imports
  "LCTR_Core_Representation_Predicate_Bridge.Core_Representation_Predicate_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Representation_Predicate_Bridge.kernel_equivalence",
  "Core_Representation_Predicate_Bridge.kernel_membership",
  "Core_Representation_Predicate_Bridge.kernel_set_exact",
  "Core_Representation_Predicate_Bridge.missing_kernel_control",
  "Core_Representation_Predicate_Bridge.missing_order_control",
  "Core_Representation_Predicate_Bridge.noninjective_control",
  "Core_Representation_Predicate_Bridge.pullback_set_exact",
  "Core_Representation_Predicate_Bridge.representation_condition_exact"
]\<close>
end
