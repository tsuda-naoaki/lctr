theory Native_Metadata_07_001
imports
  "LCTR_Core_Typed_Report_Covariance.Core_Typed_Report_Covariance"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Typed_Report_Covariance.component_maps.certificate_correspondence_exact",
  "Core_Typed_Report_Covariance.component_maps.data_equivalence_injective",
  "Core_Typed_Report_Covariance.component_maps.report_equivalence_unique_with_component_maps",
  "Core_Typed_Report_Covariance.component_maps.transformed_certificate_fields",
  "Core_Typed_Report_Covariance.component_maps.typed_readout_covariance"
]\<close>
end
