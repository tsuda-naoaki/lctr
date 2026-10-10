theory Native_Metadata_01_168
imports
  "LCTR_Native_Law_Jet_Alignment.Native_Law_Jet_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Native_Law_Jet_Alignment.generated_jet_relation_membership",
  "Native_Law_Jet_Alignment.native_jet_independent_of_extension",
  "Native_Law_Jet_Alignment.realization_value_in_chart(1)",
  "Native_Law_Jet_Alignment.realization_value_in_chart(2)",
  "Native_Law_Jet_Alignment.smooth_realizations_agree_nearby",
  "Native_Law_Jet_Alignment.time_change_preserves_native_zeroth(1)",
  "Native_Law_Jet_Alignment.time_change_preserves_native_zeroth(2)",
  "Native_Law_Jet_Alignment.time_covariance_preserves_native_membership(1)",
  "Native_Law_Jet_Alignment.time_covariance_preserves_native_membership(2)",
  "Native_Law_Jet_Alignment.value_change_acts_on_native_jet(1)",
  "Native_Law_Jet_Alignment.value_change_acts_on_native_jet(2)",
  "Native_Law_Jet_Alignment.value_covariance_preserves_native_membership(1)",
  "Native_Law_Jet_Alignment.value_covariance_preserves_native_membership(2)",
  "Native_Law_Jet_Alignment.zeroth_is_generated_curve",
  "Native_Law_Jet_Alignment.zeroth_is_native_law_value(1)",
  "Native_Law_Jet_Alignment.zeroth_is_native_law_value(2)"
]\<close>
end
