theory Native_Metadata_01_029
imports
  "LCTR_Core_Continuum_Source_Bridge.Core_Continuum_Source_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Source_Bridge.eight_conditions",
  "Core_Continuum_Source_Bridge.fibre_membership"
]\<close>
end
