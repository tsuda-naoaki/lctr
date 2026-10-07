theory Native_Metadata_01_026
imports
  "LCTR_Core_Continuum_Integration_Alignment.Core_Continuum_Integration_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Integration_Alignment.all_sat_iff_tests",
  "Core_Continuum_Integration_Alignment.approx_all_iff",
  "Core_Continuum_Integration_Alignment.approx_index_bijection",
  "Core_Continuum_Integration_Alignment.approx_predecessor_kinds",
  "Core_Continuum_Integration_Alignment.approx_states_iff_conditions",
  "Core_Continuum_Integration_Alignment.operational_first_excess",
  "Core_Continuum_Integration_Alignment.quantitative_validity"
]\<close>
end
