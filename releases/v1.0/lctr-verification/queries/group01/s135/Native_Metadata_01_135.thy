theory Native_Metadata_01_135
imports
  "LCTR_Core_Representation_Alignment.Core_Representation_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Representation_Alignment.empty_source_image",
  "Core_Representation_Alignment.imageMap_commutes",
  "Core_Representation_Alignment.imageMap_strict_order",
  "Core_Representation_Alignment.imageMap_unique",
  "Core_Representation_Alignment.imageProjection_surjective",
  "Core_Representation_Alignment.image_order_iso_exists_unique",
  "Core_Representation_Alignment.missing_kernel_control",
  "Core_Representation_Alignment.source_representation_image_uniqueness"
]\<close>
end
