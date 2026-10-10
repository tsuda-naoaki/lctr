theory Native_Metadata_01_023
imports
  "LCTR_Core_Continuum_Encoding_Alignment.Core_Continuum_Encoding_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Encoding_Alignment.final_three_margin",
  "Core_Continuum_Encoding_Alignment.first_six_preserved",
  "Core_Continuum_Encoding_Alignment.half_exact",
  "Core_Continuum_Encoding_Alignment.midpoint_encoding",
  "Core_Continuum_Encoding_Alignment.midpoint_margin",
  "Core_Continuum_Encoding_Alignment.midpoint_positive_margin",
  "Core_Continuum_Encoding_Alignment.nine_component_encoding",
  "Core_Continuum_Encoding_Alignment.source_quantitative_validity",
  "Core_Continuum_Encoding_Alignment.source_robust_validity",
  "Core_Continuum_Encoding_Alignment.wrong_threshold_controls"
]\<close>
end
