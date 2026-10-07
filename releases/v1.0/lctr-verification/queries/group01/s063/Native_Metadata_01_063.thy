theory Native_Metadata_01_063
imports
  "LCTR_Core_Frequency_Windows.Core_Frequency_Windows"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Frequency_Windows.arrival_projection.abstract_window_retains_fields",
  "Core_Frequency_Windows.arrival_projection.admissibility_iff",
  "Core_Frequency_Windows.arrival_projection.count_difference_positive",
  "Core_Frequency_Windows.arrival_projection.endpoint_is_projected_arrival",
  "Core_Frequency_Windows.native_frequency.coordinate_difference_positive",
  "Core_Frequency_Windows.native_frequency.frequency_positive",
  "Core_Frequency_Windows.native_frequency.period_invariance",
  "Core_Frequency_Windows.native_frequency.period_positive_and_product",
  "Core_Frequency_Windows.native_frequency.source_values_unique"
]\<close>
end
