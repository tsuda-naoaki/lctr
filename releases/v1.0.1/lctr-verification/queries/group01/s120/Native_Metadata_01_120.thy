theory Native_Metadata_01_120
imports
  "LCTR_Core_Quotient_Interface.Core_Quotient_Interface"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Quotient_Interface.class_interface.class_kernel",
  "Core_Quotient_Interface.class_interface.class_native_bijective",
  "Core_Quotient_Interface.class_interface.class_native_commutes",
  "Core_Quotient_Interface.class_interface.class_native_unique",
  "Core_Quotient_Interface.class_interface.class_projection_kernel",
  "Core_Quotient_Interface.class_interface.class_projection_surjective",
  "Core_Quotient_Interface.empty_class_quotient",
  "Core_Quotient_Interface.exact_pullback_requires_saturation",
  "Core_Quotient_Interface.image_least",
  "Core_Quotient_Interface.image_pullback",
  "Core_Quotient_Interface.image_unique_least",
  "Core_Quotient_Interface.native_comparison.native_comparison_projection"
]\<close>
end
