theory Native_Metadata_01_032
imports
  "LCTR_Core_Cycle_Count_Input.Core_Cycle_Count_Input"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Cycle_Count_Input.counter_distinction",
  "Core_Cycle_Count_Input.counter_update",
  "Core_Cycle_Count_Input.phase_display_correspondence",
  "Core_Cycle_Count_Input.repeated_display_allowed",
  "Core_Cycle_Count_Input.updated_correspondence"
]\<close>
end
