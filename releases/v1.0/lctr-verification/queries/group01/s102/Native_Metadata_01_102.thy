theory Native_Metadata_01_102
imports
  "LCTR_Core_Native_Law_Transport.Core_Native_Law_Transport"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Law_Transport.faithful_candidate_inverse",
  "Core_Native_Law_Transport.inverse_image_invariance",
  "Core_Native_Law_Transport.native_time_transport.base_value_bijective",
  "Core_Native_Law_Transport.native_time_transport.change_commutes",
  "Core_Native_Law_Transport.native_time_transport.change_identity_values",
  "Core_Native_Law_Transport.native_time_transport.changed_domain_contained",
  "Core_Native_Law_Transport.native_time_transport.native_admissible_family_image",
  "Core_Native_Law_Transport.native_time_transport.native_common_domain_image",
  "Core_Native_Law_Transport.native_time_transport.native_evaluation_tuple",
  "Core_Native_Law_Transport.native_time_transport.native_five_conditions",
  "Core_Native_Law_Transport.native_time_transport.new_value_injective"
]\<close>
end
