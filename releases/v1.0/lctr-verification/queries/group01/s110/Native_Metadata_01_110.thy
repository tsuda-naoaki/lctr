theory Native_Metadata_01_110
imports
  "LCTR_Core_Observer_Record_Images.Core_Observer_Record_Images"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Observer_Record_Images.observer_record_images.canonical_image_relation_inverse",
  "Core_Observer_Record_Images.observer_record_images.canonical_image_source_witness",
  "Core_Observer_Record_Images.observer_record_images.code_image_exact",
  "Core_Observer_Record_Images.observer_record_images.empty_window_images",
  "Core_Observer_Record_Images.observer_record_images.equal_code_images_same_time_images",
  "Core_Observer_Record_Images.observer_record_images.equal_code_record_in_image",
  "Core_Observer_Record_Images.observer_record_images.four_images_unique",
  "Core_Observer_Record_Images.observer_record_images.image_monotonicity",
  "Core_Observer_Record_Images.observer_record_images.injective_code_window_characterization",
  "Core_Observer_Record_Images.observer_record_images.native_record_cell_factorization",
  "Core_Observer_Record_Images.observer_record_images.nonempty_images",
  "Core_Observer_Record_Images.observer_record_images.real_image_factorization",
  "Core_Observer_Record_Images.observer_record_images.real_image_membership",
  "Core_Observer_Record_Images.observer_record_images.source_record_in_image"
]\<close>
end
