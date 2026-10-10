theory Native_Metadata_01_132
imports
  "LCTR_Core_Relative_Initial.Core_Relative_Initial"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Relative_Initial.empty_initial",
  "Core_Relative_Initial.endpoint_characterization",
  "Core_Relative_Initial.maximum_unique",
  "Core_Relative_Initial.mono_identifies",
  "Core_Relative_Initial.union_greatest",
  "Core_Relative_Initial.union_initial"
]\<close>
end
