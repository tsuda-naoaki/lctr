theory Native_Metadata_01_002
imports
  "LCTR_Core_Affine_Frequency.Core_Affine_Frequency"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Affine_Frequency.affine_frequency.coordinate_difference_positive",
  "Core_Affine_Frequency.affine_frequency.difference_nonnegative",
  "Core_Affine_Frequency.affine_frequency.difference_reflexive",
  "Core_Affine_Frequency.affine_frequency.difference_zero_iff",
  "Core_Affine_Frequency.affine_frequency.frequency_positive",
  "Core_Affine_Frequency.affine_frequency.period_positive_and_product",
  "Core_Affine_Frequency.affine_frequency.period_window_invariance",
  "Core_Affine_Frequency.affine_frequency.window_constant_value_unique",
  "Core_Affine_Frequency.count_difference_positive",
  "Core_Affine_Frequency.hz_number_positive",
  "Core_Affine_Frequency.standard_normalization",
  "Core_Affine_Frequency.zero_count_invalidates_product"
]\<close>
end
