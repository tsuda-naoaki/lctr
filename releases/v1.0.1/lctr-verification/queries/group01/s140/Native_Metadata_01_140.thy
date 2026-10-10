theory Native_Metadata_01_140
imports
  "LCTR_Core_Scale_Transport.Core_Scale_Transport"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Scale_Transport.data_transport.exceeded_image",
  "Core_Scale_Transport.data_transport.saturation_image",
  "Core_Scale_Transport.data_transport.validity_under_data_iso",
  "Core_Scale_Transport.image_of_iff",
  "Core_Scale_Transport.order_transport.initial_image",
  "Core_Scale_Transport.order_transport.least_exists_iff",
  "Core_Scale_Transport.order_transport.least_image_iff",
  "Core_Scale_Transport.order_transport.maximal_initial_image",
  "Core_Scale_Transport.scale_transport.scale_domain_and_boundary_transport"
]\<close>
end
