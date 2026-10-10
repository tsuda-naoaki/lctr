theory Native_Metadata_01_039
imports
  "LCTR_Core_Dynamic_Master.Core_Dynamic_Master"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamic_Master.native_dynamic_master.dynamic_master",
  "Core_Dynamic_Master.native_dynamic_master.same_pre_real_input"
]\<close>
end
